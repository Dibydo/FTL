class Edge:
    def __init__(self, e_from, e_to, sym):
        self.e_from = e_from
        self.e_to = e_to
        self.sym = sym

    def __repr__(self):
        temp = [self.e_from, self.e_to, self.sym]
        return "[" + ", ".join(temp) + "]"


class DFA:
    start_state = "[S]"
    final_state = "[F0]"

    def __init__(self, states: set[str], edges: set[Edge]):
        self.states = states
        self.edges = edges

    def add_state(self, state: str):
        self.states.add(state)

    def add_edge(self, e: Edge):
        self.edges.add(e)

    def __repr__(self):
        return "States:\n" + str(self.states) + "\n" + "Edges:\n" + str(self.edges)
