import networkx as nx
from slither import Slither
from a18z import verify, LegacyQuery

class State:
    def __init__(self, file) -> None:
        self._slither = Slither(file)
        self._functions = set()
        self._call_graph = nx.DiGraph()
        self._root_query = LegacyQuery()
        self._clusters = []

    @property
    def slither(self):
        return self._slither

    @property
    def functions(self):
        return self._functions

    @property
    def clusters(self):
        return self._clusters

    @property
    def call_graph(self):
        return self._call_graph

    @property
    def root_query(self):
        return self._root_query

    def add_function(self, val):
        self._functions.add(val)

    def add_edge(self, fr, to):
        self._call_graph.add_edge(fr, to)

    def add_node(self, node):
        self._call_graph.add_node(node)

    def add_cluster(self, cluster):
        self._clusters.append(cluster)