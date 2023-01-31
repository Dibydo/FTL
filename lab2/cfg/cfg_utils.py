import uuid
from copy import deepcopy
from cfg.rule import Nonterm, Term, Epsilon, Rule


def get_nterms(rules_set):
    nterms_set = set()
    for rule in rules_set:
        rule_list = [rule.left] + rule.rights
        for rule_rule in rule_list:
            if isinstance(rule_rule, Nonterm):
                nterms_set.add(rule_rule)
    return nterms_set


def get_terms(rules_set):
    terms_set = set()
    for rule in rules_set:
        rule_list = [rule.left] + rule.rights
        for rule_rule in rule_list:
            if isinstance(rule_rule, Term):
                terms_set.add(rule_rule)
    return terms_set


def remove_nterms_that_dont_present_at_left(rules):
    presenting_nterms = set()
    new_rules = set()
    for rule in rules:
        presenting_nterms.add(rule.left)
    for rule in rules:
        new_right = []
        for right in rule.rights:
            if isinstance(right, Term) or isinstance(right, Nonterm) and right in presenting_nterms:
                new_right.append(right)
        if len(new_right) == 0:
            new_right.append(Epsilon())
        new_rules.add(Rule(rule.left, new_right))
    return new_rules


def remove_rules_with_only_eps_right(rules):
    new_rules = set()
    for rule in rules:
        if all(map(lambda x: isinstance(x, Epsilon), rule.rights)):
            continue
        new_rules.add(deepcopy(rule))
    return new_rules


def split_long_rule(rule):
    new_rules = set()
    current_nterm = deepcopy(rule.left)
    new_nterm = Nonterm("[U" + uuid.uuid4().hex[:3].upper() + "]")
    for i in range(len(rule.rights) - 2):
        new_rules.add(Rule(current_nterm, [rule.rights[i], new_nterm]))
        current_nterm = new_nterm
        new_nterm = Nonterm("[U" + uuid.uuid4().hex[:3].upper() + "]")
    new_rules.add(Rule(current_nterm, [rule.rights[-2], rule.rights[-1]]))
    return new_rules

def create_unique_str():
    return f"[U{uuid.uuid4().hex[:2].upper()}]"
