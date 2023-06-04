from slither import Slither
from slither.core.declarations.function_contract import FunctionContract
from .legacy import LegacyVM, LegacyChain
from .revamp import RevampVM, RevampChain
from .path_collector import PathCollector

class Verifier:
    def __init__(self, file) -> None:
        self._slither = Slither(file)

    def revamp_precondition(self, function: FunctionContract):
        print(f'> {function.canonical_name}')
        path_collector = PathCollector()
        path_collector.collect_paths(function.entry_point)
        is_verified = True
        for path in path_collector.paths:
            chain = RevampChain()
            vm = RevampVM()
            for ir in path:
                chain.add_ir(ir)
            chain.run_chain(vm)
            print(vm.constraints)
            print(vm.postcondition)
            is_verified = is_verified and vm.is_verified()
        print(is_verified)
        if not is_verified:
            exit(0)

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
            print(vm.constraints)
            print(vm.postcondition)
            is_verified = is_verified and vm.is_verified()
        print(is_verified)
        if not is_verified:
            exit(0)
