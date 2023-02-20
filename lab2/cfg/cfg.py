import re
from cfg.cfg_utils import *
from cfg.rule import Term, Nonterm, Rule, Epsilon


class CFG_Parser():
    def __init__(self, string):
        self.string = string.replace("\n", "")

    def parse_rules(self):
        seq = self.parse_seq()
        rules_set = set()
        rules_raw = []
        arrow_index = -1
        while arrow_index:
            try:
                arrow_index = seq.index('->')
                second_arrow_index = seq.index('->', arrow_index + 1)
            except:
                rules_raw.append(seq)
                break

            rules_raw.append(seq[:second_arrow_index - 1])
            seq = seq[second_arrow_index - 1:]

        for rule_list in rules_raw:
            assert rule_list[1] == '->'
            new_rule = Rule(rule_list[0], rule_list[2:])
            rules_set.add(new_rule)

        return CFG(rules_set)

    def parse_seq(self):
        parse_results = []
        while self.string:
            to_append = self.get_nonterm() or self.get_term_or_eps() or self.get_arrow()
            if not to_append:
                break
            parse_results.append(to_append)
        if not self.string == '':
            raise Exception('ERROR: BAD INPUT')
        ret = []
        for res in parse_results:
            if res:
                ret.append(res)
        return ret

    def get_nonterm(self):
        match = re.match('^\[[A-Z,a-z]+\]', self.string)
        if not match:
            return False

        non_terminal = match.group(0)
        self.string = self.string[len(non_terminal):]
        return Nonterm(non_terminal)

    def get_term_or_eps(self):
        if self.get_start_if_exists().isalpha():
            return Term(self.get_next())
        if self.get_start_if_exists() == '_':
            self.get_next()
            return Epsilon()

    def get_arrow(self):
        if self.get_start_if_exists() == '-':
            if self.get_next() == '-' and self.get_next() == '>':
                return '->'
            else:
                raise Exception('ERROR: BAD INPUT')
        return False

    def get_start_if_exists(self):
        if self.string == '':
            return False
        return self.string[0]

    def get_next(self):
        if self.string == '':
            return False
        ret = self.string[0]
        self.string = self.string[1:]
        return ret


class CFG():
    def __init__(self, rules_set):
        self.child_relations = None
        self.parent_relations = None
        self.chain_rules = None
        self.collapsing = None
        self.reachable = None
        self.rules = rules_set
        self.terms = get_terms(rules_set)
        self.nterms = get_nterms(rules_set)

        self.start = Nonterm('[S]')
        self.build_dependency_graph()

    def __repr__(self):
        ret = ""
        for rule in self.rules:
            ret += str(rule) + '\n'
        return ret.strip()

    def build_dependency_graph(self):
        child_relations = {}
        parent_relations = {}
        for rule in self.rules:
            left = rule.left
            rights = list(filter(lambda x: isinstance(x, Nonterm), rule.rights))

            if left not in child_relations:
                child_relations[left] = set(rights)
            else:
                child_relations[left].update(rights)

            for right in rights:
                if right not in parent_relations:
                    parent_relations[right] = {left}
                else:
                    parent_relations[right].add(left)

        self.child_relations = child_relations
        self.parent_relations = parent_relations
        return self

    def toCNF(self):
        return self.remove_long_rules().remove_epsilon_rules().remove_chain_rules().remove_useless_rules().several_nonterm_removal().remove_trivial_nterms().remove_nonterms_with_single_term_transition()

    def remove_long_rules(self):
        new_rules = set()
        for rule in self.rules:
            if len(rule.rights) > 2:
                new_rules = new_rules.union(self._split_long_rule(rule))
            else:
                new_rules.add(deepcopy(rule))
        return CFG(new_rules)

    def remove_trivial_nterms(self):
        def clean_rules(rules):
            new_rules = set()

            for rule in rules:
                filtered_right_part = list(
                    filter(lambda x: not isinstance(x, Epsilon), rule.rights))
                if filtered_right_part:
                    rule.rights = filtered_right_part
                else:
                    rule.rights = [Epsilon()]
                new_rules.add(rule)
            return new_rules

        rules = clean_rules(self.rules)

        nterms = self.nterms

        while True:
            nterms_num = len(nterms)

            for nterm in nterms:
                nterms_rules = list(filter(lambda x: x.left == nterm, rules))
                if not nterms_rules:
                    continue
                if all(map(lambda x: x.rights == [Epsilon()], nterms_rules)):
                    rewrittent_rules = set()
                    for rule in rules:
                        rule.rights = list(
                            map(lambda x: x if x != nterm else Epsilon(), rule.rights))
                        rewrittent_rules.add(rule)
                    rules = rewrittent_rules

                    nterms.remove(nterm)
                    rules = list(filter(lambda x: nterm != x.left, rules))
                    break

            rules = clean_rules(rules)

            if len(nterms) == nterms_num:
                break

        return CFG(rules)

    def remove_epsilon_rules(self):
        new_rules = deepcopy(self.rules)
        new_rules = self.remove_rules_with_only_eps_right(new_rules)
        self._find_collapsing()
        if (self.start in self.collapsing):
            new_rules.add(Rule(Nonterm("[S]"), [Epsilon()]))

        new_rules = new_rules.union(
            self._gen_all_possible_combinations_of_rules(new_rules))
        new_rules = self.remove_rules_with_only_eps_right(
            self.remove_nterms_that_dont_present_at_left(new_rules))
        if (self.start in self.collapsing):
            new_rules.add(Rule(Nonterm("[S]"), [Epsilon()]))
        return CFG(new_rules)

    def _gen_all_possible_combinations_of_rules(self, rules):
        combinations = set()
        for rule in rules:
            if any(map(lambda x: x in self.collapsing, rule.rights)):
                right_comb = self._gen_right_side_combinations(
                    rule.rights, [], 0)
                for comb in right_comb:
                    combinations.add(Rule(rule.left, comb))
        return combinations

    def _gen_right_side_combinations(self, right, current_c, current_i):
        if (current_i == len(right)):
            if (all(map(lambda x: isinstance(x, Epsilon), current_c))):
                return []
            return [current_c]
        tmp = []
        if (right[current_i] in self.collapsing):
            tmp += self._gen_right_side_combinations(
                right, current_c + [Epsilon()], current_i + 1)
        tmp += self._gen_right_side_combinations(
            right, current_c + [right[current_i]], current_i + 1)
        return tmp

    def remove_nterms_that_dont_present_at_left(self, rules):
        presenting_nterms = set()
        new_rules = set()
        for rule in rules:
            presenting_nterms.add(rule.left)
        for rule in rules:
            new_right = []
            for right in rule.rights:
                if (isinstance(right, Term) or isinstance(right, Nonterm) and right in presenting_nterms):
                    new_right.append(right)
            if (len(new_right) == 0):
                new_right.append(Epsilon())
            new_rules.add(Rule(rule.left, new_right))
        return new_rules

    def _find_collapsing(self):
        self.collapsing = set()
        flag = True
        tmp = deepcopy(self.rules)
        while flag:
            flag = False
            for rule in tmp:
                if (len(rule.rights) == 1 and isinstance(rule.rights[0], Epsilon)):
                    flag = True
                    self.collapsing.add(rule.left)
                    tmp.remove(rule)
                    break
                if all(map(lambda x: isinstance(x, Nonterm), rule.rights)) and all(
                        map(lambda x: x in self.collapsing, rule.rights)):
                    self.collapsing.add(rule.left)
                    flag = True
                    tmp.remove(rule)
                    break
        return self

    def remove_rules_with_only_eps_right(self, rules):
        new_rules = set()
        for rule in rules:
            if (all(map(lambda x: isinstance(x, Epsilon), rule.rights))):
                continue
            new_rules.add(deepcopy(rule))
        return new_rules

    def _split_long_rule(self, rule):
        new_rules = set()
        current_nterm = deepcopy(rule.left)
        new_nterm = Nonterm("[U" + uuid.uuid4().hex[:3].upper() + "]")
        for i in range(len(rule.rights) - 2):
            new_rules.add(Rule(current_nterm, [rule.rights[i], new_nterm]))
            current_nterm = new_nterm
            new_nterm = Nonterm("[U" + uuid.uuid4().hex[:3].upper() + "]")
        new_rules.add(Rule(current_nterm, [rule.rights[-2], rule.rights[-1]]))
        return new_rules

    def remove_chain_rules(self):
        self._find_chain_rules()
        chainrules = self.ChR
        if len(self.nterms) == len(chainrules):
            return self
        rules = set()
        for rule in self.rules:
            left = rule.left
            rights = rule.rights
            if len(rights) == 1 and type(rights[0]) == Nonterm and [left.name, rights[0].name] in chainrules:
                pass
            else:
                rules.add(rule)
        copy_rules = deepcopy(rules)
        for ch in chainrules:
            for rule in copy_rules:
                left = rule.left
                rights = rule.rights
                if ch[1] == left.name:
                    rules.add(Rule(Nonterm(ch[0]), rights))
        return CFG(rules)

    def _find_chain_rules(self):
        chainrules = []
        for nterm in self.nterms:
            chainrules.append([nterm.name, nterm.name])
        while True:
            upow = len(chainrules)
            for rule in self.rules:
                left = rule.left
                rights = rule.rights
                if len(rights) == 1 and type(rights[0]) == Nonterm:
                    r = rights[0]
                    for ch in chainrules:
                        if ch[1] == left.name:
                            pair = [ch[0], r.name]
                            if not pair in chainrules:
                                chainrules.append(pair)
            new_upow = len(chainrules)
            if upow == new_upow:
                break
        self.ChR = chainrules

    def remove_useless_rules(self):
        return self.remove_nongenerating_rules().remove_unreachable_symbols()

    def several_nonterm_removal(self):
        def create_unique_str():
            return f"[U{uuid.uuid4().hex[:2].upper()}]"

        rules = set()
        new_rules = []
        to_symbol = {}
        for rule in self.rules:
            left = rule.left
            rights = rule.rights
            if len(rights) == 1 or all(map(lambda x: isinstance(x, Nonterm), rights)):
                new_rules.append(rule)
                continue
            rights_new = []
            for r in deepcopy(rights):
                if isinstance(r, Term):
                    if not r.symbol in to_symbol.keys():
                        new_nterm = create_unique_str()
                        to_symbol[r.symbol] = new_nterm
                        new_rules.append(
                            Rule(Nonterm(new_nterm), [Term(r.symbol)]))
                        rights_new.append(Nonterm(new_nterm))
                    else:
                        rights_new.append(Nonterm(to_symbol[r.symbol]))
                else:
                    rights_new.append(r)
            new_rules.append(Rule(left, rights_new))
        return CFG(new_rules)

    def remove_nonterms_with_single_term_transition(self):
        useless_nterm = {}
        for nt in self.nterms:
            useless_nterm[nt.name] = None
        for rule in self.rules:
            left = rule.left
            rights = rule.rights
            if len(rights) == 1 and isinstance(rights[0], Term) and left.name in useless_nterm.keys() and useless_nterm[
                left.name] == None:
                useless_nterm[left.name] = rights[0].symbol
                continue
            useless_nterm.pop(left.name, None)

        new_rules = set()
        for rule in self.rules:
            left = rule.left
            rights = rule.rights
            new_rights = []
            for r in rights:
                if isinstance(r, Nonterm) and r.name in useless_nterm.keys():
                    new_rights.append(Term(useless_nterm[r.name]))
                    continue
                new_rights.append(r)
            new_rules.add(Rule(left, new_rights))
        return CFG(new_rules)

    def remove_nongenerating_rules(self):
        genetaring_nterm = set()
        for rule in self.rules:
            left = rule.left
            rights = rule.rights
            if all(map(lambda x: isinstance(x, Term), rights)):
                genetaring_nterm.add(left.name)
        while True:
            upow = len(genetaring_nterm)
            for rule in self.rules:
                left = rule.left
                rights = rule.rights
                flag = True
                for r in rights:
                    if isinstance(r, Nonterm) and not r.name in genetaring_nterm:
                        flag = False
                        break
                if flag:
                    genetaring_nterm.add(left.name)

            new_upow = len(genetaring_nterm)
            if upow == new_upow:
                break
        new_rules = []
        for rule in self.rules:
            rights = rule.rights
            if any(map(lambda x: isinstance(x, Nonterm) and not x.name in genetaring_nterm, rights)):
                continue
            new_rules.append(rule)
        return CFG(new_rules)

    def remove_unreachable_symbols(self):
        self.reachable = {self.start}
        unallocated = self.nterms.difference(self.reachable)

        while True:
            upow = len(unallocated)

            unallocated_copy = deepcopy(unallocated)
            for nterm in unallocated_copy:
                if nterm in self.parent_relations and set(self.parent_relations[nterm]) & self.reachable:
                    self.reachable.add(nterm)
                    unallocated.remove(nterm)

            new_upow = len(unallocated)

            if new_upow == upow:
                break

        new_rules = set(filter(
            lambda x: x.left in self.reachable,
            self.rules
        ))

        return CFG(new_rules)