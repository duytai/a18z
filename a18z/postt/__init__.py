import z3
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from .chain import PosttChain
from .vm import PosttVM

def posttcondition(function: FunctionContract):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    outcomes = []
    for path in path_collector.paths:
        chain = PosttChain()
        vm = PosttVM()
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm)
        vm.finalize(function)
        outcomes.append(vm.outcomes)
    return z3.simplify(z3.Or(outcomes))