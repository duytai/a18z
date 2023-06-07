import networkx as nx
from slither.slithir.operations import InternalCall

from .state import State
from ..legacy import verify
from ..pre import precondition

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
    def execute(self, state: State):
        if state.all_verified():
            print('Hum? all are verified')
            return
        functions = list(nx.topological_sort(state.call_graph))[::-1]
        for function in functions:
            if not verify(function):
                pre_ = precondition(function)
                query = {
                    function.canonical_name: (pre_, None)
                }
                state.all_verified(query)
                break