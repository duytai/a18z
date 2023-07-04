import z3
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from ..legacy import LegacyQuery
from .chain import PreChain
from .vm import PreVM
    
def precondition(function: FunctionContract, postcondition=None, query: LegacyQuery=LegacyQuery()):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    facts = None
    num_paths = len(path_collector.paths)
    for path in path_collector.paths:
        chain = PreChain()
        vm = PreVM(postcondition, num_paths)
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm, query)
        vm.finalize(function)
        if vm.facts is not None:
            if facts is None:
                facts = vm.facts
            else:
                facts = z3.simplify(z3.Or(facts, vm.facts))
    return facts