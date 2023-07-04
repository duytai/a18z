import sexpdata
import networkx as nx
import z3
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
        for f in state.functions:
            collect(f, state.root_query)
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
class RQ3(Task):
    def execute(self, state: State):
        queries = []
        for function in state.functions:
            query = LegacyQuery()
            query.add_precondition(function, z3.BoolVal(True))
            queries.append(query)
            query = LegacyQuery()
            query.add_postcondition(function, z3.BoolVal(False))
            queries.append(query)
        for query in queries:
            clusters = []
            visited = set()
            func_map = dict((f.canonical_name, verify(f, query)) for f in state.functions)
            for node in state.call_graph.nodes:
                if not func_map[node] and node not in visited:
                    selected = [node]
                    selected += nx.descendants(state.call_graph.to_undirected(), node)
                    visited = visited.union(set(selected))
                    graph = nx.subgraph(state.call_graph, selected)
                    cluster = list(reversed(list(nx.topological_sort(graph))))
                    clusters.append(cluster)
            print('....')
            print(query)
            print(clusters)
            state._clusters = clusters
            ff = FixFunction()
            ff.execute(state, query)
            print('---> FINISH <---')

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
    min_query = None
    min_acc = None
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

    def update_patch(self, pending: List[str], query: LegacyQuery, state: State, acc: int):
        print(f'LLEN: {len(pending)}')
        if not pending:
            yield query, acc
        else:
            func_map = dict((f.canonical_name, f) for f in state.functions)
            func = func_map[pending.pop(0)]
            print(f'FUNC {func.canonical_name}')
            if verify(func, query):
                print('NO-CHANGE')
                yield from self.update_patch(pending[::], copy(query), state, acc)
                return
            # Fix precondition
            print('COMPUTE-PRE')
            new_pre = precondition(func, query=query)
            if new_pre is not None:
                print('NEW-PRE')
                new_acc = acc
                old_pre = state.root_query.get_precondition(func)
                x = sexpdata.loads(old_pre.sexpr())
                x = self.build_graph(x)
                y = sexpdata.loads(new_pre.sexpr())
                y = self.build_graph(y)
                new_acc += nx.graph_edit_distance(x, y, timeout=2) + 20
                if new_acc < self.min_acc:
                    print('ADD-PRE')
                    pre_query = copy(query)
                    pre_query.add_precondition(func, new_pre)
                    yield from self.update_patch(pending[::], pre_query, state, new_acc)
            # Fix postcondition
            print('COMPUTE-POST')
            new_post = postcondition(func, query=query)
            if new_post is not None:
                print('NEW-POST')
                new_acc = acc
                old_post = state.root_query.get_postcondition(func)
                x = sexpdata.loads(old_post.sexpr())
                x = self.build_graph(x)
                y = sexpdata.loads(new_post.sexpr())
                y = self.build_graph(y)
                new_acc += nx.graph_edit_distance(x, y, timeout=2) + 20
                if new_acc < self.min_acc:
                    print('ADD-POST')
                    post_query = copy(query)
                    post_query.add_postcondition(func, new_post)
                    yield from self.update_patch(pending[::], post_query, state, new_acc)
            # Internal function call
            # for node in func.nodes:
            #     for ir in node.irs:
            #         if isinstance(ir, InternalCall):
            #             if not ir.is_modifier_call:
            #                 prep = prepcondition(ir, query)
            #                 if prep is not None:
            #                     new_acc = acc
            #                     new_pre, new_post = prep
            #                     # new precondition
            #                     old_pre = state.root_query.get_precondition(func)
            #                     x = sexpdata.loads(old_pre.sexpr())
            #                     x = self.build_graph(x)
            #                     y = sexpdata.loads(new_pre.sexpr())
            #                     y = self.build_graph(y)
            #                     new_acc += nx.graph_edit_distance(x, y, timeout=2) + 20
            #                     # new postcondition
            #                     old_post = state.root_query.get_postcondition(func)
            #                     x = sexpdata.loads(old_post.sexpr())
            #                     x = self.build_graph(x)
            #                     y = sexpdata.loads(new_post.sexpr())
            #                     y = self.build_graph(y)
            #                     new_acc += nx.graph_edit_distance(x, y, timeout=2) + 20
            #                     # update prep
            #                     if new_acc < self.min_acc:
            #                         prep_query = copy(query)
            #                         prep_query.add_precondition(ir.function, new_pre)
            #                         prep_query.add_postcondition(ir.function, new_post)
            #                         yield from self.update_patch(pending[::], prep_query, state, new_acc)

    def execute(self, state: State, init=LegacyQuery()):
        queries = []
        func_map = dict((f.canonical_name, f) for f in state.functions)
        for cluster in state.clusters:
            self.min_query = None
            self.min_acc = 1000
            for query, acc in tqdm(self.update_patch(cluster[::], init, state, 0)):
                # verify patch
                ok = True
                for name in cluster:
                    ok = ok and verify(func_map[name], query)
                print('****')
                print(query)
                print(ok)
                print('****')
                if not ok: continue
                if acc < self.min_acc:
                    self.min_acc = acc
                    self.min_query = query
            assert self.min_query is not None
            queries.append(self.min_query)
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
            pre_ = precondition(function)
            query = LegacyQuery()
            query.add_precondition(function, pre_)
            print(query)
            if not verify(function, query):
                raise ValueError('??')