from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from .chain import LegacyChain
from .vm import LegacyVM
from .query import LegacyQuery

def verify(function: FunctionContract, query: LegacyQuery = LegacyQuery()):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    is_verified = True
    for path in path_collector.paths:
        chain = LegacyChain()
        vm = LegacyVM(
            precondition=query.get_precondition(function),
            postcondition=query.get_postcondition(function)
        )
        for ir in path: chain.add_ir(ir)
        chain.run_chain(vm, query)
        vm.finalize(function)
        is_verified = is_verified and vm.is_verified
    return is_verified