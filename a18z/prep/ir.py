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
            marker_vars = [vm.fresh_variable(x) for x in ir.function.parameters]
            param_vars = [vm.get_variable(x) for x in ir.function.parameters]
            for x, y, z in zip(marker_vars, arguments, param_vars):
                vm.add_constraint(x == y)
                vm.add_prep_substitution((x, z))

            # Find all variables
            variables = z3.z3util.get_vars(vm.constraints)

            # Find eliminated variables
            state_vars = [x.name for x in ir.function.state_variables_read]
            curr_state_vars = [x.name for x in ir.node.function.state_variables_read]
            eliminated_state_vars = list(set(curr_state_vars) - set(state_vars))

            curr_local_vars = [x.name for x in ir.node.function.local_variables]
            curr_param_vars = [x.name for x in ir.node.function.parameters]
            marker_vars = [str(x) for x in marker_vars]
            curr_temp_vars = [str(x) for x in variables if str(x).startswith('c!')]
            eliminated_vars = curr_local_vars + curr_temp_vars + curr_param_vars + eliminated_state_vars
            eliminated_vars = [x for x in variables if str(x) in eliminated_vars and str(x) not in marker_vars]

            outcome = find_outcome(vm.constraints, eliminated_vars)
            vm.prep = (z3.substitute(outcome, vm.prep_substitutions), None)

            # Set return value to 
            if ir.lvalue:
                assert len(ir.function.returns) == 1
                ret = vm.get_variable(ir.function.returns[0])
                value = vm.fresh_variable(ir.lvalue)
                vm.set_variable(ir.lvalue, value)
                vm.add_prep_substitution((value, ret))
        elif ir.function == vm.internal_call.function:
            print(f'***** {ir.function}')
            super().execute(vm)
        else:
            super().execute(vm)