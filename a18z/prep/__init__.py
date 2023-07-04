from copy import copy
from slither.slithir.operations import InternalCall
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from ..legacy import LegacyQuery, verify
from .vm import PrepVM
from .chain import PrepChain
    
def prepcondition(call: InternalCall, query: LegacyQuery = LegacyQuery()):
    function = call.node.function
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    for path in path_collector.paths:
        chain = PrepChain()
        vm = PrepVM(call)
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm, query)
        vm.finalize(function)
        if vm.prep:
            pre_, post_ = vm.prep
            query_ = copy(query)
            query_.add_precondition(function, pre_)
            query_.add_postcondition(function, post_)
            if verify(call.function, query_):
                return tuple(vm.prep)