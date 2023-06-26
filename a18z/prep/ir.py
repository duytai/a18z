import z3
from ..legacy.ir import LegacyInternalCall
from ..legacy.vm import LegacyVM
from ..legacy.utils import check_sat
from ..legacy.query import LegacyQuery
from ..post.utils import find_outcome
from ..pre import precondition as find_pre
from ..post import postcondition as find_post
from .vm import PrepVM
from slither.slithir.operations import InternalCall, LibraryCall

class PrepInternalCall(LegacyInternalCall):
    def execute(self, vm: PrepVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, (InternalCall, LibraryCall))
        if isinstance(ir, InternalCall) and ir.is_modifier_call:
            print(f'#### {ir.function}')
            return
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
            if outcome is not None:
                vm.add_prep(z3.substitute(outcome, vm.prep_substitutions))
                # Set return value to
                if ir.lvalue:
                    assert len(ir.function.returns) == 1
                    ret = vm.get_variable(ir.function.returns[0])
                    value = vm.fresh_variable(ir.lvalue)
                    vm.set_variable(ir.lvalue, value)
                    vm.add_prep_substitution((value, ret))
            else:
                vm.rev = True
        elif ir.function == vm.internal_call.function:
            pre_ = find_pre(
                vm.internal_call.function,
                postcondition=z3.BoolVal(True)
            )
            post_ = find_post(
                vm.internal_call.function,
                precondition=pre_
            )
            if pre_ is not None and post_ is not None:
                # A trick if variable has been set
                if ir.lvalue and ir.lvalue not in vm._variables:
                    value = vm.fresh_variable(ir.lvalue)
                    vm.set_variable(ir.lvalue, value)
                call_vm = LegacyVM(
                    precondition=pre_,
                    postcondition=post_
                )
                # Read precondition
                for i in ir.function.nodes[1].irs:
                    self._chain.add_ir(i)
                self._chain.run_chain(call_vm, query)
                # Subtitute parameters with arguments
                parameters = ir.function.parameters + ir.function.returns
                arguments = ir.arguments + [ir.lvalue]
                substitutions = []
                for param, argument in zip(parameters, arguments):
                    old_var = call_vm.get_variable(param)
                    new_var = vm.get_variable(argument)
                    substitutions.append((old_var, new_var))
                # Imply precondition
                precondition = z3.substitute(call_vm.precondition, *substitutions)
                vm.rev = check_sat(z3.Not(z3.Implies(vm.constraints, precondition)))
                # Read postcondition
                for i in ir.function.nodes[2].irs:
                    self._chain.add_ir(i)
                self._chain.run_chain(call_vm, query)
                # Handle old_
                for new_var, old_var in call_vm.olds:
                    vm.substitute(new_var, old_var)
                postcondition = z3.substitute(call_vm.postcondition, *substitutions)
                vm.add_constraint(postcondition)
            else:
                self.rev = True
        else:
            super().execute(vm, query)