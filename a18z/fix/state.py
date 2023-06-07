import networkx as nx
from slither import Slither
from ..legacy import verify, LegacyQuery

class State:
    def __init__(self, file) -> None:
        self._slither = Slither(file)
        self._functions = set()
        self._call_graph = nx.DiGraph()
        self._internal_calls = []

    @property
    def slither(self):
        return self._slither

    @property
    def functions(self):
        return self._functions

    @property
    def call_graph(self):
        return self._call_graph

    @property
    def internal_calls(self):
        return self._internal_calls

    def all_verified(self, query: LegacyQuery) -> bool:
        is_verified = True
        for function in self._functions:
            r = verify(function, query)
            if not r:
                print(f'failed> {function}')
            is_verified = is_verified and r
        return is_verified

    def add_function(self, val):
        self._functions.add(val)

    def add_edge(self, fr, to):
        self._call_graph.add_edge(fr, to)

    def add_node(self, node):
        self._call_graph.add_node(node)

    def add_internal_call(self, ir):
        self._internal_calls.append(ir)
