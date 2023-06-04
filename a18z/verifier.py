import z3
from slither import Slither
from slither.core.declarations.function_contract import FunctionContract
from .legacy import LegacyVM, LegacyChain
from .revamp import RevampVM, RevampChain
from .morden import MordenVM, MordenChain
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
            chain = MordenChain()
            vm = MordenVM()
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
            chain = RevampChain()
            vm = RevampVM()
            for ir in path:
                chain.add_ir(ir)
            chain.run_chain(vm)
            facts.append(vm.facts)
        fact = z3.simplify(z3.Or(facts))
        print(fact)

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
