import z3
from slither.slithir.operations import InternalCall
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from .vm import PrepVM
from .chain import PrepChain
    
def prepcondition(call: InternalCall, query=None):
    function = call.node.function
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    prep = []
    for path in path_collector.paths:
        chain = PrepChain()
        vm = PrepVM(call)
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm, query)
        vm.finalize(function)
        if vm.prep: prep.append(tuple(vm.prep))
    return prep