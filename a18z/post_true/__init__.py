import z3
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from .chain import PostTrueChain
from .vm import PostTrueVM

def postruecondition(function: FunctionContract):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    outcomes = []
    for path in path_collector.paths:
        chain = PostTrueChain()
        vm = PostTrueVM()
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm)
        vm.finalize(function)
        outcomes.append(vm.outcomes)
    return z3.simplify(z3.Or(outcomes))