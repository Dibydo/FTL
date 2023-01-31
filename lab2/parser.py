from cfg.cfg import CFG_Parser
from dfa.dfa import DFA, Edge


def read_input(input_filename):
    with open(input_filename, "r", encoding="utf-8") as file_input:
        rules = file_input.readlines()

    rules = [rule.strip() for rule in rules]
    clear_rules = rule_gen(rules)
    cfg_result = ""
    for rule in clear_rules:
        if rule == 0:
            break
        non_terminal, right_from_arrow = rule.split("->")
        non_terminal = non_terminal.strip()

        right_from_arrow_arr = right_from_arrow.split("|")
        right_from_arrow_arr = [elem.strip() for elem in right_from_arrow_arr]

        for elem in right_from_arrow_arr:
            cfg_result += non_terminal + "->" + elem + "\n"

    a = CFG_Parser(cfg_result)
    c = a.parse_rules().to_chomsky_norm_form()

    states = {"[F0]"}
    edges = set()

    for rule in clear_rules:
        if rule == 0:
            break
        non_terminal, right_from_arrow = rule.split("->")
        st_from = non_terminal.strip()
        states.add(st_from)

        right_from_arrow_arr = right_from_arrow.split("|")

        for t in right_from_arrow_arr:
            t = t.strip()
            sym = t[0]
            t = t[1:]
            if t:
                st_to = t
            else:
                st_to = "[F0]"
            states.add(st_to)
            e = Edge(st_from, st_to, sym)
            edges.add(e)

    dfa = DFA(states, edges)

    return c, dfa


def rule_gen(rules: list[str]):
    rules = rules[1:]
    for rule in rules:
        ret = rule.strip()
        if ret[0] != "[":
            yield 0
        else:
            yield ret
