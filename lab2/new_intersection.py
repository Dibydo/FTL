from cfg.rule import *

class Scalar:
    def __init__(self, p, non_term, q):
        self.p = p
        self.non_term = non_term
        self.q = q
        self.reachable = False
        self.producing = False

    def __str__(self):
        j = ", ".join([str(self.p), str(self.non_term), str(self.q)])
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
terminals = []
rules = []
terminalRules = []
nonterms = []
starting = Scalar


def markReachables(s):
    added = 0
    for ir in rules:
        if ir.left == s:
            for rpt in ir.rights:
                for nt in nonterms:
                    if nt == rpt and not nt.reachable:
                        added += 1
                        nt.reachable = True
                        added += markReachables(nt)
                        break
    return added



def removeUnreachableNonterminals():
    count_reachable = 1
    count_to_compare = 1
    starting.reachable = True
    count_reachable += markReachables(starting)
    while count_reachable != count_to_compare:
        count_to_compare = count_reachable
        count_reachable += markReachables(starting)
    for r in rules[:]:
        if r in terminalRules:
            for nt in nonterms:
                if nt == r.left and not nt.reachable:
                    rules.remove(r)
                    terminalRules.remove(r)
                    break
        else:
            for rpt in r.rights:
                if rpt not in nonterms:
                    rules.remove(r)
            for nt in nonterms:
                if nt == r.left and not nt.reachable:
                    rules.remove(r)
    for nt in nonterms[:]:
        if not nt.reachable:
            nonterms.remove(nt)


def markProducing():
    added = 0
    for ir in rules:
        for nt in nonterms:
            if nt == ir.left:
                if not nt.producing:
                    prod = True
                    for rpt in ir.rights:
                        for nt2 in nonterms:
                            if rpt == nt2 and not nt2.producing:
                                prod = False
                                break
                    if prod:
                        added += 1
                        nt.producing = True
    return added


def removeUnproducingNonterminals():
    count_producing = 0
    count_to_compare = 0
    for r in rules:
        if len(r.rights) == 1:
            for nt in nonterms:
                if nt == r.left:
                    nt.producing = True
                    count_producing += 1
                    break
    count_producing += markProducing()
    while count_producing != count_to_compare:
        count_to_compare = count_producing
        count_producing += markProducing()
    for r in rules[:]:
        for nt in nonterms:
            if nt == r.left and not nt.producing:
                rules.remove(r)
    for nt in nonterms[:]:
        if not nt.producing:
            nonterms.remove(nt)


def make_intersection(cfg, dfa):
    global starting
    states = dfa.states
    cfg_nonterms = cfg.nterms
    cfg_rules = cfg.rules
    transitions = dfa.edges
    starting = Scalar(dfa.start_state, cfg.start, dfa.final_state)
    nonterms.append(starting)
    build_terminal_rules(cfg_rules, transitions)
    build_nonterminal_rules(cfg_rules, transitions, states)
    oldRuleSize = len(rules)
    while not (len(rules) == oldRuleSize):
        oldRuleSize = len(rules)
        removeUnreachableNonterminals()
        removeUnproducingNonterminals()
        newRuleSize = len(rules)
        if oldRuleSize != newRuleSize:
            removeUnreachableNonterminals()
            newNewRuleSize = len(nonterms)
            if newNewRuleSize != newRuleSize:
                removeUnproducingNonterminals()

    return rules

def build_terminal_rules(cfg_rules, transitions):
    for rule in cfg_rules:
        if is_to_term(rule):
            term = rule.rights[0]
            if term not in terminals:
                terminals.append(term)
            nonterm = rule.left
            for tr in transitions:
                if tr.sym == term.symbol:
                    newNonterm = Scalar(tr.e_from, nonterm, tr.e_to)
                    right_part = []
                    right_part.append(term)
                    newRule = []
                    for s in right_part:
                        newRule.append(IntersectionRule(newNonterm, [s]))
                    # newRule = IntersectionRule(newNonterm, RP)
                    rules.extend(newRule)
                    terminalRules.extend(newRule)
                    # if :
                    #     nonterms.append(newNonterm)
                    is_add = False
                    for nt in nonterms:
                        if nt.p == newNonterm.p:
                            is_add = True
                        if nt.q == newNonterm.q:
                            is_add = True
                        if nt.non_term == newNonterm.non_term:
                            is_add = True
                    if not is_add:
                        nonterms.append(newNonterm)


def build_nonterminal_rules(cfg_rules, transitions, states):
    for r in rules:
        if is_to_nonterm_nonterm(r):
            right1 = r.rights[0]
            right2 = r.rights[1]
            for p in states:
                for q in states:
                    left = Scalar(p, r.left, q)
                    if CheckForProducing(left, cfg_rules):
                        for qi in states:
                            RPleft = Scalar(p, right1, qi)
                            if CheckForProducing(RPleft, cfg_rules):
                                temp = False
                                for nt in nonterms:
                                    if nt.p == RPleft.p:
                                        temp = True
                                    if nt.q == RPleft.q:
                                        temp = True
                                    if nt.non_term == RPleft.non_term:
                                        temp = True
                                if not temp:
                                    nonterms.append(RPleft)
                                RPright = Scalar(qi, right2, q)
                                if CheckForProducing(RPright, cfg_rules):
                                    bbr = False
                                    for nt in nonterms:
                                        if nt.p == RPright.p:
                                            bbr = True
                                        if nt.q == RPleft.q:
                                            bbr = True
                                        if nt.non_term == RPleft.non_term:
                                            bbr = True
                                    if not bbr:
                                        nonterms.append(RPright)
                                    bo = False
                                    for tr in terminalRules:
                                        if tr.left == left:
                                            bo = True
                                    if RPleft == left and bo:
                                        continue
                                    if RPright == left and bo:
                                        continue
                                    RP = []
                                    RP.append(RPleft)
                                    RP.append(RPright)
                                    newRule = IntersectionRule(left, RP)
                                    rules.append(newRule)



def is_to_term(rule):
    return len(rule.rights) == 1 and isinstance(rule.rights[0], Term)


def is_to_empty(rule):
    return len(rule.right) == 1 and isinstance(rule.right[0], Epsilon)


def is_to_nonterm_nonterm(rule):
    return len(rule.right) == 2 and isinstance(rule.right[0], Nonterm) and isinstance(rule.right[1], Nonterm)


def CheckForProducing(left, cfg_rules):
    isNotOnlyToTerm = False
    isNotProducing = True
    for r2 in cfg_rules:
        if r2.left == left.non_term and (not is_to_term(r2) or is_to_empty(r2)):
            isNotOnlyToTerm = True
            isNotProducing = False
            break
    if not isNotOnlyToTerm:
        for termR in terminalRules:
            if termR.left == left:
                isNotProducing = False
                break
    if not isNotProducing:
        return True
    else:
        return False

