from cfg.cfg import CFG
from cfg.rule import Rule, Term, Nonterm, Epsilon
from dfa.dfa import DFA, Edge


class ScalObj:
    def __init__(self, p, Nont, q):
        self.p = p
        self.Nont = Nont
        self.q = q

    def __str__(self):
        j = ", ".join([self.p, str(self.Nont), self.q])
        return "<" + j + ">"

    def __repr__(self):
        return self.__str__()

    def __hash__(self):
        return hash(self.p) + hash(self.Nont) + hash(self.q)

    def __eq__(self, o):
        return isinstance(o, ScalObj) and self.p == o.p and self.Nont == o.Nont and self.q == o.q


class IntersectionRule:
    def __init__(self, left: ScalObj, right: list[ScalObj | str]):
        self.left = left
        self.right = right

    def __str__(self):
        r = "".join(map(str, self.right))
        return str(self.left) + " -> " + r

    def __repr__(self):
        return self.__str__()


def find_intersection(cfg: CFG, dfa: DFA):
    intersection: set[IntersectionRule] = set()

    first_set_nont = set()
    rules: set[Rule] = set()

    # Сначала породим терминальные правила
    for rule in cfg.rules:
        if len(rule.rights) == 1:
            first_set_nont.add(rule.left)
            for trans in dfa.edges:
                if trans.sym == rule.rights[0].symbol:
                    obj = ScalObj(trans.e_from, rule.left, trans.e_to)
                    new_rule = IntersectionRule(obj, [trans.sym])
                    intersection.add(new_rule)
        else:
            rules.add(rule)
    # вроде породили

    terminal_only_nonterms: set[Nonterm] = set()
    for nont in first_set_nont:
        for r in rules:
            if r.left == nont:
                break
        else:
            terminal_only_nonterms.add(nont)
    term_rules = intersection.copy()

    # По каждому правилу A -> A1..An из cfg строим правила
    # <p,A,q> -> <p,A,q1><q1,A,q> для всех возможных p,q,q1
    for rule in rules:
        for p in dfa.states:
            for q in dfa.states:
                for q1 in dfa.states:
                    s1 = ScalObj(p, rule.left, q)
                    s2 = ScalObj(p, rule.rights[0], q1)
                    s3 = ScalObj(q1, rule.rights[1], q)
                    f = False
                    if p == "[S]" and q1 == "[R]" and q == "[F0]":
                        f = True
                    if not rule_legit([s1, s2, s3], terminal_only_nonterms, term_rules, dfa.edges, f):
                        continue
                    int_rule = IntersectionRule(s1, [s2, s3])
                    intersection.add(int_rule)

    # тут почистим
    start = ScalObj(dfa.start_state, Nonterm("[S]"), dfa.final_state)
    result = find_result(intersection, start)

    result = tam_bil_ne_result_vot_result(result, dfa.final_state)
    return result


def find_result(intersection: set[IntersectionRule], start: ScalObj):
    final_scals = {start}
    final_intersection = set()
    flag = True  # мы добавляли правило на прошлой итерации?
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


def rule_legit(objs: list[ScalObj],
               terminal_only_nonterms: set[Nonterm],
               term_rules: set[IntersectionRule],
               edges_possible: set[Edge],
               f):
    if objs[0] == objs[1] or objs[0] == objs[2]:
        for rule in term_rules:
            if objs[0].p == rule.left.p and objs[0].Nont == rule.left.Nont:

                break
        else:
            return False
    for obj in objs[1:]:
        for edge in edges_possible:
            if obj.p == edge.e_from and obj.q == edge.e_to:
                break
        else:
            return False
        if obj.Nont not in terminal_only_nonterms:
            continue
        for rule in term_rules:
            if obj == rule.left:
                break
        else:
            return False
    return True


def tam_bil_ne_result_vot_result(result: set[IntersectionRule], final_state_dfa: str):
    # print(result)
    start = ScalObj("[S]", Nonterm("[S]"), final_state_dfa)
    to_check = [start]
    checked_rules: set[IntersectionRule] = set()
    while to_check:
        next_obj = to_check.pop()
        rules = find_rules(next_obj, result)
        for rule in rules:
            if rule in checked_rules:
                continue
            if check_rule(rule, result):
                checked_rules.add(rule)
                if len(rule.right) == 2:
                    to_check.append(rule.right[0])
                    to_check.append(rule.right[1])
            else:
                result.remove(rule)
                start = ScalObj("[S]", Nonterm("[S]"), final_state_dfa)
                to_check = [start]
                checked_rules = set()
    return checked_rules


def check_rule(rule: IntersectionRule, rules: set[IntersectionRule]):
    # проверить, что в правой части терминал
    if len(rule.right) == 1:
        return True
    # или оба нетерминала имеют какое-то правило
    for n in rule.right:
        if not find_rules(n, rules):
            return False
    return True


def find_rules(obj: ScalObj, rules: set[IntersectionRule]):
    result = []
    for rule in rules:
        if rule.left == obj:
            result.append(rule)
    return result
