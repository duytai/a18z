import z3
from slither.slithir.operations import SolidityCall
from slither.core.declarations.solidity_variables import SolidityFunction
from ..legacy.ir import LegacySolidityCall
from .vm import RevampVM
from .utils import find_fact


class RevampSolidityCall(LegacySolidityCall):
    def execute(self, vm: RevampVM):
        ir = self._ir
        assert isinstance(ir, SolidityCall)
        if ir.function == SolidityFunction('assert(bool)'):
            postcondition = vm.get_variable(ir.arguments[0])
            substitutions = []
            for x, y in dict(vm.substitutions[::-1]).items():
                substitutions += [(x, y), (y, x)]
            constraints = z3.substitute(vm.constraints, *substitutions)
            postcondition = z3.substitute(postcondition, *substitutions)
            # A variables
            variables = z3.z3util.get_vars(z3.And(constraints, postcondition))  
            local_vars = [x.name for x in ir.node.function.local_variables]
            temporary_vars = [str(x) for x in variables if str(x).startswith('c!')]
            eliminated_vars = local_vars + temporary_vars
            eliminated_vars = [x for x in variables if str(x) in eliminated_vars]
            fact = find_fact(constraints, postcondition, eliminated_vars)
            vm.add_fact(fact)
        else: super().execute(vm)