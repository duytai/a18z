import z3
from ..legacy.ir import LegacyInternalCall
from ..post.utils import find_outcome
from .vm import PrepVM
from slither.slithir.operations import InternalCall

class PrepInternalCall(LegacyInternalCall):
    def execute(self, vm: PrepVM):
        ir = self._ir
        assert isinstance(ir, InternalCall)
        if ir == vm.internal_call:
            arguments = [vm.get_variable(x) for x in ir.arguments]
            
            # Find all variables
            variables = z3.z3util.get_vars(vm.constraints)
            for argument in arguments:
                variables += z3.z3util.get_vars(argument)
            variables = set(variables)

            # Find eliminated variables
            local_vars = [x.name for x in ir.node.function.local_variables]
            param_vars = [x.name for x in ir.node.function.parameters]
            temporary_vars = [str(x) for x in variables if str(x).startswith('c!')]
            eliminated_vars = local_vars + temporary_vars + param_vars
            eliminated_vars = [x for x in variables if str(x) in eliminated_vars]
            
            markers = [vm.fresh_variable(x) for x in ir.function.parameters]
            constraints = z3.And([x == y for x, y in zip(markers, arguments)])
            constraints = z3.And(vm.constraints, constraints)

            print(constraints)
            print(eliminated_vars)
            ok = find_outcome(constraints, eliminated_vars)
            print(ok)
            raise ValueError('??')
        super().execute(vm)