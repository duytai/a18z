import z3
from slither import Slither
from slither.slithir.operations import InternalCall
from slither.core.declarations.function_contract import FunctionContract
from .legacy import LegacyVM, LegacyChain
from .pre import PreVM, PreChain
from .post import PostVM, PostChain
from .prep import PrepChain, PrepVM
from .path_collector import PathCollector


class Verifier:
    def __init__(self, file) -> None:
        self._slither = Slither(file)

    def postcondition(self, function: FunctionContract):
        print(f'> {function.canonical_name}')
        path_collector = PathCollector()
        path_collector.collect_paths(function.entry_point)
        outcomes = []
        for path in path_collector.paths:
            chain = PostChain()
            vm = PostVM()
            for ir in path:
                chain.add_ir(ir)
            chain.run_chain(vm)
            outcomes.append(vm.outcomes)
        outcome = z3.simplify(z3.Or(outcomes))
        print(outcome)

    def precondition(self, function: FunctionContract):
        print(f'> {function.canonical_name}')
        path_collector = PathCollector()
        path_collector.collect_paths(function.entry_point)
        facts = []
        for path in path_collector.paths:
            chain = PreChain()
            vm = PreVM()
            for ir in path:
                chain.add_ir(ir)
            chain.run_chain(vm)
            facts.append(vm.facts)
        fact = z3.simplify(z3.Or(facts))
        print(fact)

    def prepcondition(self, function: FunctionContract):
        print(f'> {function.canonical_name}')
        path_collector = PathCollector()
        path_collector.collect_paths(function.entry_point)
        # Collect all internal calls
        internal_calls = []
        for node in function.nodes:
            for ir in node.irs:
                if isinstance(ir, InternalCall):
                    internal_calls.append(ir)
        # Compute for each function call
        for internal_call in internal_calls:
            for path in path_collector.paths:
                chain = PrepChain()
                vm = PrepVM(internal_call)
                for ir in path:
                    chain.add_ir(ir)
                chain.run_chain(vm)


    def verify_function(self, function: FunctionContract):
        print(f'> {function.canonical_name}')
        path_collector = PathCollector()
        path_collector.collect_paths(function.entry_point)
        is_verified = True
        for path in path_collector.paths:
            chain = LegacyChain()
            vm = LegacyVM()
            for ir in path:
                chain.add_ir(ir)
            chain.run_chain(vm)
            is_verified = is_verified and vm.is_verified
        if not is_verified:
            exit(0)
