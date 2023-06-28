import sexpdata
import networkx as nx
from tqdm import tqdm
from copy import copy
from timeit import default_timer as timer
from slither.slithir.operations import InternalCall, LibraryCall
from colorist import Color
from typing import List

from a18z.fix.state import State
from .state import State
from a18z import (
    LegacyQuery,
    precondition,
    postcondition,
    prepcondition,
    collect,
    verify
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
        for contract in state.slither.contracts:
            for function in contract.functions:
                if function in state.functions:
                    state.add_node(function.canonical_name)
                    for node in function.nodes:
                        for ir in node.irs:
                            if isinstance(ir, InternalCall):
                                if not ir.is_modifier_call:
                                    state.add_edge(function.canonical_name, ir.function.canonical_name)
                            elif isinstance(ir, LibraryCall):
                                state.add_edge(function.canonical_name, ir.function.canonical_name)

class BuildCluster(Task):
    def execute(self, state: State):
        visited = set()
        func_map = dict((f.canonical_name, verify(f)) for f in state.functions)
        for node in state.call_graph.nodes:
            if not func_map[node] and node not in visited:
                selected = [node]
                selected += nx.descendants(state.call_graph.to_undirected(), node)
                visited = visited.union(set(selected))
                graph = nx.subgraph(state.call_graph, selected)
                cluster = list(reversed(list(nx.topological_sort(graph))))
                state.add_cluster(cluster)

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

    def update_patch(self, pending: List[str], query: LegacyQuery, state: State):
        if not pending:
            yield query
        else:
            func_map = dict((f.canonical_name, f) for f in state.functions)
            func = func_map[pending.pop(0)]
            if verify(func, query):
                # No fix
                yield from self.update_patch(pending[::], copy(query), state)
            # Fix precondition
            pre_ = precondition(func, query=query)
            if pre_ is not None and str(pre_) != 'False':
                pre_query = copy(query)
                pre_query.add_precondition(func, pre_)
                yield from self.update_patch(pending[::], pre_query, state)
            # Fix postcondition
            post_ = postcondition(func, query=query)
            if post_ is not None and str(post_) != 'True':
                post_query = copy(query)
                post_query.add_postcondition(func, post_)
                yield from self.update_patch(pending[::], post_query, state)
            # Internal function call
            for node in func.nodes:
                for ir in node.irs:
                    if isinstance(ir, InternalCall):
                        if not ir.is_modifier_call:
                            prep = prepcondition(ir, query)
                            if prep is not None:
                                pre_, post_ = prep
                                prep_query = copy(query)
                                prep_query.add_precondition(ir.function, pre_)
                                prep_query.add_postcondition(ir.function, post_)
                                yield from self.update_patch(pending[::], prep_query, state)

    def execute(self, state: State):
        queries = []
        func_map = dict((f.canonical_name, f) for f in state.functions)
        root_query = LegacyQuery()
        for f in state.functions:
            collect(f, root_query)
        for cluster in state.clusters:
            result_query = None
            result_acc = None
            for query in tqdm(self.update_patch(cluster[::], LegacyQuery(), state)):
                # check if the query is ok
                ok = True
                for name in cluster:
                    ok = ok and verify(func_map[name], query)
                if not ok: continue
                # if ok, we proceed
                acc = 0
                for name, new_pre in query.preconditions.items():
                    old_pre = root_query.get_precondition(func_map[name])
                    x = sexpdata.loads(old_pre.sexpr())
                    x = self.build_graph(x)
                    y = sexpdata.loads(new_pre.sexpr())
                    y = self.build_graph(y)
                    acc += nx.graph_edit_distance(x, y, node_match=lambda x, y: x == y)
                    acc += 20
                for name, new_post in query.postconditions.items():
                    old_post = root_query.get_postcondition(func_map[name])
                    x = sexpdata.loads(old_post.sexpr())
                    x = self.build_graph(x)
                    y = sexpdata.loads(new_post.sexpr())
                    y = self.build_graph(y)
                    acc += nx.graph_edit_distance(x, y, node_match=lambda x, y: x == y)
                    acc += 20
                if result_acc is None:
                    result_acc = acc
                    result_query = query
                elif acc < result_acc:
                    result_acc = acc
                    result_query = query
            assert result_query is not None
            queries.append(result_query)
        for query in queries:
            print(query)

class EvaluateInference(Task):
    def execute(self, state: State):
        print('::: Precondition :::')
        start = timer()
        p_value = 0
        for function in state.functions:
            # if not verify(function):
            print(f'> Function {function.canonical_name}')
                # print(f'> Verified: {verify(function)}')
            pre_ = precondition(function)
            print(f'{Color.YELLOW}{pre_}{Color.OFF}')
            if str(pre_) != 'True':
                p_value += 1
        end = timer()
        print(f'#F: {len(state.functions)}')
        print(f'#D: {end - start}')
        print(f'#P: {p_value} ({round(p_value / len(state.functions) * 100)})')
        print('::: Postcondition :::')
        start = timer()
        p_value = 0
        for function in state.functions:
            print(f'> Function {function.canonical_name}')
            post_ = postcondition(function)
            print(f'{Color.YELLOW}{post_}{Color.OFF}')
            if str(post_) != 'False':
                p_value += 1
        end = timer()
        print(f'#F: {len(state.functions)}')
        print(f'#d: {end - start}')
        print(f'#Q: {p_value} ({round(p_value / len(state.functions) * 100)})')


class EvaluateCallsite(Task):
    def execute(self, state: State):
        start = timer()
        p_value = 0
        goods = 0
        for function in state.functions:
            print(f'> {function.canonical_name}')
            for node in function.nodes:
                for ir in node.irs:
                    if isinstance(ir, (InternalCall, LibraryCall)):
                        if not hasattr(ir, 'is_modifier_call') or not ir.is_modifier_call:
                            r = prepcondition(ir)
                            if r:
                                print(r)
                                [(p, q)] = r
                                query = LegacyQuery()
                                query.add_precondition(ir.function, p)
                                query.add_postcondition(ir.function, q)
                                print(verify(ir.function))
                                goods += 1
                            else:
                                print(ir)
                            p_value += 1
        end = timer()
        print(f'#internal: {p_value}')
        print(f'#success: {goods}')
        print(f'#d: {end - start}')


class TestFunction(Task):
    def execute(self, state: State):
        for function in state.functions:
            print(f'> {Color.YELLOW}{function.canonical_name}{Color.OFF}')
            print(verify(function))