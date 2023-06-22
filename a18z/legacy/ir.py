import z3
from slither.slithir.operations import (
    Binary,
    Assignment,
    BinaryType,
    Condition,
    Unary,
    Index,
    InternalCall,
    SolidityCall,
    Transfer,
    Send,
    TypeConversion,
    LibraryCall
)
from slither.slithir.operations.high_level_call import HighLevelCall
from slither.core.expressions.unary_operation import UnaryOperationType
from slither.slithir.operations.return_operation import Return
from slither.slithir.variables.reference import ReferenceVariable
from slither.core.declarations.solidity_variables import SolidityFunction
from a18z.legacy.query import LegacyQuery

from a18z.legacy.vm import LegacyVM
from .vm import LegacyVM
from .utils import check_sat
from .query import LegacyQuery

class LegacyIR:
    def __init__(self, _ir):
        self._ir = _ir

    def execute(self, vm: LegacyVM, query: LegacyQuery): pass

class LegacyBinary(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Binary)
        lvar = vm.get_variable(ir.variable_left)
        rvar = vm.get_variable(ir.variable_right)
        if ir.type == BinaryType.SUBTRACTION:
            result = lvar - rvar
        elif ir.type == BinaryType.ADDITION:
            result = lvar + rvar
        elif ir.type == BinaryType.EQUAL:
            result = lvar == rvar
        elif ir.type == BinaryType.NOT_EQUAL:
            result = lvar != rvar
        elif ir.type == BinaryType.LESS_EQUAL:
            result = lvar <= rvar
        elif ir.type == BinaryType.LESS:
            result = lvar < rvar
        elif ir.type == BinaryType.GREATER_EQUAL:
            result = lvar >= rvar
        elif ir.type == BinaryType.GREATER:
            result = lvar > rvar
        elif ir.type == BinaryType.ANDAND:
            result = z3.And(lvar, rvar)
        elif ir.type == BinaryType.OROR:
            result = z3.Or(lvar, rvar)
        elif ir.type == BinaryType.MULTIPLICATION:
            result = lvar * rvar
        elif ir.type == BinaryType.DIVISION:
            result = lvar / rvar
        elif ir.type == BinaryType.MODULO:
            result = lvar % rvar
        elif ir.type == BinaryType.POWER:
            result = z3.ToInt(lvar**rvar)
        else: raise ValueError(ir.type)
        if isinstance(ir.lvalue, ReferenceVariable):
            lvar = vm.get_variable(ir.lvalue)
            assert z3.is_select(lvar)
            base, index = lvar.children()
            if z3.is_select(base):
                root, _ = base.children()
                tmp = vm.substitute(root)
                result = z3.Store(base, index, result)
                result = z3.substitute(result, (root, tmp))
                vm.add_constraint(base == result)
                return
            rvar = z3.Store(base, index, result)
            tmp = vm.substitute(base)
            rvar = z3.substitute(rvar, (base, tmp))
            vm.add_constraint(base == rvar)
            return
        vm.set_variable(ir.lvalue, result)

class LegacyAssignment(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Assignment)
        if isinstance(ir.lvalue, ReferenceVariable):
            rvar = vm.get_variable(ir.rvalue)
            lvar = vm.get_variable(ir.lvalue)
            assert z3.is_select(lvar)
            base, index = lvar.children()
            if z3.is_select(base):
                root, _ = base.children()
                tmp = vm.substitute(root)
                result = z3.Store(base, index, rvar)
                result = z3.substitute(result, (root, tmp))
                vm.add_constraint(base == result)
                return
            rvar = z3.Store(base, index, rvar)
            tmp = vm.substitute(base)
            rvar = z3.substitute(rvar, (base, tmp))
            vm.add_constraint(base == rvar)
            return
        lvar = vm.get_variable(ir.lvalue)
        if str(lvar) == '__v1':
            rvar = vm.get_variable(ir.rvalue)
            vm.set_precondition(rvar)
        elif str(lvar) == '__v2':
            rvar = vm.get_variable(ir.rvalue)
            vm.set_postcondition(rvar)
        else:
            vm.substitute(lvar)
            rvar = vm.get_variable(ir.rvalue)
            vm.add_constraint(lvar == rvar)

class LegacyCondition(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Condition)
        rvar = vm.get_variable(ir.value)
        vm.add_constraint(rvar)

class LegacyUnary(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Unary)
        rvar = vm.get_variable(ir.rvalue)
        if ir.type == UnaryOperationType.BANG:
            vm.set_variable(ir.lvalue, z3.Not(rvar))
        else: raise ValueError(ir.type)

class LegacyIndex(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Index)
        lvar = vm.get_variable(ir.variable_left)
        rvar = vm.get_variable(ir.variable_right)
        vm.set_variable(ir.lvalue, z3.Select(lvar, rvar))

class LegacyInternalCall(LegacyIR):
    def __init__(self, _ir, _chain):
        super().__init__(_ir)
        self._chain = _chain

    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, (InternalCall, LibraryCall))
        if hasattr(ir, 'is_modifier_call') and ir.is_modifier_call:
            print(f'#### {ir.function}')
            return
        # A trick if variable has been set
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

class LegacyHighLevelCall(LegacyIR):
    def __init__(self, _ir, _chain):
        super().__init__(_ir)
        self._chain = _chain

    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, HighLevelCall)
        # TODO
        if ir.lvalue and ir.lvalue not in vm._variables:
            value = vm.fresh_variable(ir.lvalue)
            vm.set_variable(ir.lvalue, value)

class LegacyReturn(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Return)
        for lvalue, rvalue in zip(ir.function.returns, ir.values):
            lvar = vm.get_variable(lvalue)
            vm.substitute(lvar)
            rvar = vm.get_variable(rvalue)
            vm.add_constraint(lvar == rvar)

class LegacySolidityCall(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, SolidityCall)
        if ir.function == SolidityFunction('assert(bool)'):
            assertion = vm.get_variable(ir.arguments[0])
            vm.rev = check_sat(z3.Not(z3.Implies(vm.constraints, assertion)))
        elif ir.function == SolidityFunction('require(bool)'):
            precondition = vm.get_variable(ir.arguments[0])
            vm.add_constraint(precondition)
        elif ir.function == SolidityFunction('require(bool,string)'):
            precondition = vm.get_variable(ir.arguments[0])
            vm.add_constraint(precondition)
        else: raise ValueError(ir.function)

class LegacyTransfer(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Transfer)
        # TODO: handle transfer
    
class LegacySend(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, Send)
        rvar = z3.BoolVal(True)
        vm.set_variable(ir.lvalue, rvar)

class LegacyTypeConversion(LegacyIR):
    def execute(self, vm: LegacyVM, query: LegacyQuery):
        ir = self._ir
        assert isinstance(ir, TypeConversion)
        rvar = vm.get_variable(ir.variable)
        vm.set_variable(ir.lvalue, rvar)