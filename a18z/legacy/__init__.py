from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from .chain import LegacyChain
from .vm import LegacyVM

def verify(function: FunctionContract):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    is_verified = True
    for path in path_collector.paths:
        chain = LegacyChain()
        vm = LegacyVM()
        for ir in path: chain.add_ir(ir)
        chain.run_chain(vm)
        vm.finalize(function)
        is_verified = is_verified and vm.is_verified
    return is_verified