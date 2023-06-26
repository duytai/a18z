import z3
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from ..legacy import LegacyQuery
from .chain import PostChain
from .vm import PostVM

def postcondition(function: FunctionContract, precondition=None, query: LegacyQuery=LegacyQuery()):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    outcomes = None
    for path in path_collector.paths:
        chain = PostChain()
        vm = PostVM(precondition)
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm, query)
        vm.finalize(function)
        if vm.outcomes is not None:
            if outcomes is not None:
                outcomes = z3.simplify(z3.Or(outcomes, vm.outcomes))
            else:
                outcomes = vm.outcomes
    return outcomes