from slither import Slither
from slither.core.declarations.function_contract import FunctionContract
from .legacy import LegacyVM, LegacyChain
from .path_collector import PathCollector

class Verifier:
    def __init__(self, file) -> None:
        self._slither = Slither(file)

    def verify_function(self, function: FunctionContract):
        path_collector = PathCollector()
        path_collector.collect_paths(function.entry_point)
        is_verified = True
        for path in path_collector.paths:
            legacy_chain = LegacyChain()
            vm = LegacyVM()
            for ir in path:
                legacy_chain.add_ir(ir)
            legacy_chain.run_chain(vm)
            is_verified = is_verified and vm.is_verified()
        print(is_verified)