import z3
from slither.core.declarations.function_contract import FunctionContract
from ..path_collector import PathCollector
from ..legacy import LegacyQuery
from .chain import PreChain
from .vm import PreVM
from .utils import find_fact
    
def precondition(function: FunctionContract, postcondition=None, query: LegacyQuery=LegacyQuery()):
    path_collector = PathCollector()
    path_collector.collect_paths(function.entry_point)
    # facts = None
    vms, subt = [], {}
    for path in path_collector.paths:
        chain = PreChain()
        vm = PreVM(postcondition)
        for ir in path:
            chain.add_ir(ir)
        chain.run_chain(vm, query)
        subt.update(dict(vm.olds + vm.substitutions))
        vms.append(vm)
    for x, y in subt.items():
        subt[x] = z3.FreshConst(y.sort())
    all_constraints = []
    assertions = []
    for vm in vms:
        constraints = z3.substitute(vm.constraints, *subt.items())
        postcondition = z3.substitute(vm.postcondition, *subt.items())
        all_subt = vm.olds + vm.substitutions + list(subt.items())
        all_subt = [(y, x) for (x, y) in dict(all_subt[::-1]).items()]
        constraints = z3.substitute(constraints, *all_subt)
        postcondition = z3.substitute(postcondition, *all_subt)
        assert z3.is_and(constraints)
        assertions += [x for x in constraints.children() if z3.is_implies(x)]
        constraints = z3.And([x for x in constraints.children() if not z3.is_implies(x)])
        all_constraints.append(constraints)
    #
    postcondition = z3.And(assertions + [postcondition])
    all_constraints = z3.Or(all_constraints)
    variables = z3.z3util.get_vars(z3.And(all_constraints, postcondition))  
    local_vars = [x.name for x in function.local_variables]
    temporary_vars = [str(x) for x in variables if str(x).startswith('c!')]
    eliminated_vars = local_vars + temporary_vars
    eliminated_vars = [x for x in variables if str(x) in eliminated_vars]
    return find_fact(all_constraints, postcondition, eliminated_vars)