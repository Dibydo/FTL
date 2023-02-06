from copy import deepcopy

from cfg.rule import Rule, Nonterm, Term


class Scalar:
    def __init__(self, p, non_term, q):
        self.p = p
        self.non_term = non_term
        self.q = q

    def __str__(self):
        j = ", ".join([self.p, str(self.non_term), self.q])
        return "<" + j + ">"

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash(self.p) + hash(self.non_term) + hash(self.q)

    def __eq__(self, o):
        return isinstance(o, Scalar) and self.p == o.p and self.non_term == o.non_term and self.q == o.q


class IntersectionRule:
    def __init__(self, left: Scalar, right: list[Scalar | str]):
        self.left = left
        self.right = right

    def __str__(self):
        r = ""
        for a in self.right:
            r += str(a)
        return str(self.left) + " -> " + r

    def __repr__(self):
        return self.__str__()


def find_intersection(cfg, dfa):
    intersection: set[IntersectionRule] = set()

    non_term_set = set()
    rules: set[Rule] = set()
    rule_left_dict = dict()
    for rule in cfg.rules:
        if rule.left not in rule_left_dict:
            rule_left_dict[rule.left] = 1
        else:
            rule_left_dict[rule.left] += 1
    single_use_term = set()
    for key in rule_left_dict:
        if rule_left_dict[key] == 1:
            single_use_term.add(key)

    single_use_rules = set()
    for a in single_use_term:
        for b in cfg.rules:
            if a == b.left:
                single_use_rules.add(b)

    for single_use_rule in single_use_rules:
        if single_use_rule in cfg.rules:
            cfg.rules.remove(single_use_rule)

    changed_rules = set()
    for rule in cfg.rules:
        for single_use_rule in single_use_rules:
            new_right = []
            for right in rule.rights:
                if right == single_use_rule.left:
                    for a in single_use_rule.rights:
                        new_right.append(a)
                else:
                    new_right.append(right)
            changed_rules.add(Rule(rule.left, new_right))

    changed_rules_2 = deepcopy(changed_rules)
    for rule in changed_rules:
        for right in rule.rights:
            for single_use_rule in single_use_rules:
                for single_use_right in single_use_rule.rights:
                    if right == single_use_rule.left and single_use_right == rule.left:
                        changed_rules_2.remove(rule)

    changed_rules_3 = deepcopy(changed_rules_2)
    for rule in changed_rules_2:
        for right in rule.rights:
            for single_use_rule in single_use_rules:
                if single_use_rule.left == right and len(single_use_rule.rights) == 1 and type(
                        single_use_rule.rights[0]) == Term:
                    new_right = []
                    for right_1 in rule.rights:
                        if right_1 != single_use_rule.left:
                            new_right.append(right_1)
                        else:
                            new_right.append(single_use_rule.rights[0])
                    changed_rules_3.remove(rule)
                    changed_rules_3.add(Rule(rule.left, new_right))
    cfg.rules = changed_rules_3

    for rule in cfg.rules:
        if len(rule.rights) == 1:
            non_term_set.add(rule.left)
            for edge in dfa.edges:
                if edge.sym == rule.rights[0].symbol:
                    scalar = Scalar(edge.e_from, rule.left, edge.e_to)
                    new_rule = IntersectionRule(scalar, [edge.sym])
                    intersection.add(new_rule)
        else:
            rules.add(rule)

    terminal_only_nonterms: set[Nonterm] = set()
    for non_term in non_term_set:
        for r in rules:
            if r.left == non_term:
                break
        else:
            terminal_only_nonterms.add(non_term)
    term_rules = intersection.copy()

    for rule in rules:
        for p in dfa.states:
            for q in dfa.states:
                for q1 in dfa.states:
                    s1 = Scalar(p, rule.left, q)
                    s2 = Scalar(p, rule.rights[0], q1)
                    s3 = Scalar(q1, rule.rights[1], q)
                    if not check_rule_right([s1, s2, s3], terminal_only_nonterms, term_rules, dfa.edges):
                        continue
                    int_rule = IntersectionRule(s1, [s2, s3])
                    intersection.add(int_rule)

    start = Scalar(dfa.start_state, Nonterm("[S]"), dfa.final_state)
    result = find_result(intersection, start)

    start = Scalar("[S]", Nonterm("[S]"), "[F0]")
    to_check = [start]
    checked_rules = set()
    while to_check:
        next_obj = to_check.pop()
        rules_temp = find_rules(next_obj, result)
        for rule in rules_temp:
            if rule in checked_rules:
                continue
            if check_rule(rule, result):
                checked_rules.add(rule)
                if len(rule.right) == 2:
                    to_check.append(rule.right[0])
                    to_check.append(rule.right[1])
            else:
                result.remove(rule)
                start = Scalar("[S]", Nonterm("[S]"), "[F0]")
                to_check = [start]
                checked_rules = set()
    result = checked_rules

    bad_result = set()
    for rule in checked_rules:
        for right in rule.right:
            if rule.left == right and not (goes_to_nonterm(checked_rules, rule.left)):
                bad_result.add(rule)
    for res in bad_result:
        if res in result:
            result.remove(res)
    return result


def goes_to_nonterm(rules, rule):
    for rule_1 in rules:
        if rule_1.left == rule and any(type(elem) == str for elem in rule_1.right):
            return True
    return False


def find_result(intersection, start):
    final_scals = {start}
    final_intersection = set()
    flag = True
    while flag:
        flag = False
        r = None
        for rule in intersection:
            if rule.left in final_scals:
                flag = True
                if len(rule.right) == 2:
                    final_scals.add(rule.right[0])
                    final_scals.add(rule.right[1])
                r = rule
                break
        if r:
            final_intersection.add(r)
            intersection.remove(r)
    return final_intersection


def check_rule_right(objs, terminal_only_nonterms, term_rules, edges_possible):
    if objs[0] == objs[1] or objs[0] == objs[2]:
        for rule in term_rules:
            if objs[0].p == rule.left.p and objs[0].non_term == rule.left.non_term:
                break
        else:
            return False
    for obj in objs:
        for edge in edges_possible:
            if obj.p == edge.e_from and obj.q == edge.e_to:
                break
        else:
            return False
        if obj.non_term not in terminal_only_nonterms:
            continue
        for rule in term_rules:
            if obj == rule.left:
                break
        else:
            return False
    return True


def check_rule(rule, rules):
    if len(rule.right) == 1:
        return True
    for a in rule.right:
        if not find_rules(a, rules):
            return False
    return True


def find_rules(obj, rules):
    result = []
    for rule in rules:
        if rule.left == obj:
            result.append(rule)
    return result
