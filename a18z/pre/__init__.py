import z3
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from .chain import PreChain
from .vm import PreVM
    
def precondition(function: FunctionContract, postcondition=None):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    facts = []
    for path in path_collector.paths:
        chain = PreChain()
        vm = PreVM(postcondition=postcondition)
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm)
        vm.finalize(function)
        facts.append(vm.facts)
    return z3.simplify(z3.Or(facts))