import sexpdata
import networkx as nx
from slither.slithir.operations import InternalCall
from .state import State
from a18z import (
    precondition,
    postcondition,
    prepcondition,
    LegacyQuery,
    collect
)

class Task:
    def execute(self, state: State): pass

class EnumerateFunction(Task):
    def execute(self, state: State):
        for contract in state.slither.contracts:
            for function in contract.functions:
                if function.contract_declarer == contract:
                    if function.is_implemented and not function.is_empty:
                        state.add_function(function)

class BuildCallGraph(Task):
    def execute(self, state: State):
        func_map = dict((f.canonical_name, f) for f in state.functions)
        for contract in state.slither.contracts:
            for function in contract.functions:
                if function in state.functions:
                    state.add_node(function)
                    for node in function.nodes:
                        for ir in node.irs:
                            if isinstance(ir, InternalCall):
                                call = func_map[ir.function.canonical_name]
                                state.add_edge(function, call)

class BuildInternalCall(Task):
    def execute(self, state: State):
        for function in state.functions:
            for node in function.nodes:
                for ir in node.irs:
                    if isinstance(ir, InternalCall):
                        state.add_internal_call(ir)

class FixFunction(Task):
    def build_graph(self, sexpr):
        def add_node(expr, G: nx.Graph):
            node, *args = expr if isinstance(expr, list) else [expr]
            n = G.number_of_nodes()
            G.add_node(n, label=node)
            G.graph[n] = node
            for arg in args:
                G.add_edge(n, add_node(arg, G))
            return n
        G = nx.Graph()
        add_node(sexpr, G)
        return G

    def execute(self, state: State):
        if state.is_verified():
            print('Hum? all are verified')
            return
        root_query = LegacyQuery()
        for function in state.functions:
            collect(function, root_query)
        # Fix pre
        for function in state.functions:
            pre_ = precondition(function)
            query = LegacyQuery()
            query.add_precondition(function, pre_)
            if state.is_verified(query):
                print(f'{query} @ True')
            else:
                print(f'{query} @ False')
        # Fix post
        for function in state.functions:
            post_ = postcondition(function)
            query = LegacyQuery()
            query.add_postcondition(function, post_)
            if state.is_verified(query):
                print(f'{query} @ True')
            else:
                print(f'{query} @ False')
        # Function call
        for function in state.functions:
            for node in function.nodes:
                for ir in node.irs:
                    if isinstance(ir, InternalCall):
                        for pre_, post_ in prepcondition(ir):
                            query = LegacyQuery()
                            query.add_precondition(ir.function, pre_)
                            query.add_postcondition(ir.function, post_)
                            if state.is_verified(query):
                                print(f'{query} @ True')
                            else:
                                print(f'{query} @ False')
