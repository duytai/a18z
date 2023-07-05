import z3
from slither.slithir.operations import (
    SolidityCall,
    InternalCall,
    LibraryCall
)
from slither.core.declarations.solidity_variables import SolidityFunction
from ..legacy.vm import LegacyVM
from ..legacy.query import LegacyQuery
from ..legacy.ir import (
    LegacySolidityCall,
    LegacyInternalCall
)
from .vm import PreVM
from .utils import find_fact


class PreSolidityCall(LegacySolidityCall):
    def execute(self, vm: PreVM, query: LegacyQuery):
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
        else: super().execute(vm, query)

class PreInternalCall(LegacyInternalCall):
    def execute(self, vm: PreVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, (InternalCall, LibraryCall))
        if isinstance(ir, InternalCall) and ir.is_modifier_call:
            #print(f'#### {ir.function}')
            return
        if ir.lvalue and ir.lvalue not in vm._variables:
            value = vm.fresh_variable(ir.lvalue)
            vm.set_variable(ir.lvalue, value)
        call_vm = LegacyVM(	
            precondition=query.get_precondition(ir.function),	
            postcondition=query.get_postcondition(ir.function)	
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
        precondition = z3.substitute(call_vm.precondition, *substitutions)
        # Synthesize fact (aka precondition)
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
        self._chain.run_chain(call_vm, query)
        # Handle old_
        for new_var, old_var in call_vm.olds:
            vm.substitute(new_var, old_var)
        postcondition = z3.substitute(call_vm.postcondition, *substitutions)
        vm.add_constraint(postcondition)