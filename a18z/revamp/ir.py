import z3
from slither.slithir.operations import (
    SolidityCall,
    InternalCall
)
from slither.core.declarations.solidity_variables import SolidityFunction
from ..legacy.vm import LegacyVM
from ..legacy.ir import (
    LegacySolidityCall,
    LegacyInternalCall
)
from ..legacy.utils import check_sat
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

class RevampInternalCall(LegacyInternalCall):
    def execute(self, vm: RevampVM):
        ir = self._ir
        assert isinstance(ir, InternalCall)
        if ir.lvalue: vm.fresh_variable(ir.lvalue)
        call_vm = LegacyVM()
        # Read precondition
        for i in ir.function.nodes[1].irs:
            self._chain.add_ir(i)
        self._chain.run_chain(call_vm)
        
        # Subtitute parameters with arguments
        parameters = ir.function.parameters + ir.function.returns
        arguments = ir.arguments + [ir.lvalue]
        substitutions = []
        for param, argument in zip(parameters, arguments):
            old_var = call_vm.get_variable(param)
            new_var = vm.get_variable(argument)
            substitutions.append((old_var, new_var))
        precondition = z3.substitute(call_vm.precondition, *substitutions)
        
        # Synthesize fatc (aka precondition)
        constraints = vm.constraints
        reversed_subs = []
        for x, y in dict(vm.substitutions[::-1]).items():
            reversed_subs += [(x, y), (y, x)]
            
        constraints = z3.substitute(vm.constraints, *reversed_subs)
        postcondition = z3.substitute(precondition, *reversed_subs)

        variables = z3.z3util.get_vars(z3.And(constraints, postcondition))  
        local_vars = [x.name for x in ir.node.function.local_variables]
        temporary_vars = [str(x) for x in variables if str(x).startswith('c!')]
        eliminated_vars = local_vars + temporary_vars
        eliminated_vars = [x for x in variables if str(x) in eliminated_vars]
        fact = find_fact(constraints, postcondition, eliminated_vars)
        vm.add_fact(fact)

        # Read postcondition
        for i in ir.function.nodes[2].irs:
            self._chain.add_ir(i)
        self._chain.run_chain(call_vm)
        # Handle old_
        for new_var, old_var in call_vm.olds:
            vm.substitute(new_var, old_var)
        postcondition = z3.substitute(call_vm.postcondition, *substitutions)
        vm.add_constraint(postcondition)