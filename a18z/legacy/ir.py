import z3
from slither.slithir.operations import (
    Binary,
    Assignment,
    BinaryType,
    Condition,
    Unary,
    UnaryType,
    Index,
    InternalCall
)
from slither.slithir.variables.reference import ReferenceVariable
from .vm import LegacyVM
from .utils import check_sat

class LegacyIR:
    def __init__(self, _ir):
        self._ir = _ir

    def execute(self, vm: LegacyVM): pass

class LegacyBinary(LegacyIR):
    def execute(self, vm: LegacyVM):
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
        elif ir.type == BinaryType.GREATER_EQUAL:
            result = lvar >= rvar
        elif ir.type == BinaryType.GREATER:
            result = lvar > rvar
        elif ir.type == BinaryType.ANDAND:
            result = z3.And(lvar, rvar)
        else: raise ValueError(ir.type)
        if isinstance(ir.lvalue, ReferenceVariable):
            lvar = vm.get_variable(ir.lvalue)
            assert z3.is_select(lvar)
            base, index = lvar.children()
            rvar = z3.Store(base, index, result)
            tmp = vm.substitute(base)
            rvar = z3.substitute(rvar, (base, tmp))
            vm.add_constraint(base == rvar)
            return
        vm.set_variable(ir.lvalue, result)

class LegacyAssignment(LegacyIR):
    def execute(self, vm: LegacyVM):
        ir = self._ir
        assert isinstance(ir, Assignment)
        if isinstance(ir.lvalue, ReferenceVariable):
            lvar = vm.get_variable(ir.lvalue)
            assert z3.is_select(lvar)
            base, index = lvar.children()
            rvar = vm.get_variable(ir.rvalue)
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
    def execute(self, vm: LegacyVM):
        ir = self._ir
        assert isinstance(ir, Condition)
        rvar = vm.get_variable(ir.value)
        vm.add_constraint(rvar)

class LegacyUnary(LegacyIR):
    def execute(self, vm: LegacyVM):
        ir = self._ir
        assert isinstance(ir, Unary)
        rvar = vm.get_variable(ir.rvalue)
        if ir.type == UnaryType.BANG:
            vm.set_variable(ir.lvalue, z3.Not(rvar))
        else: raise ValueError(ir.type)

class LegacyIndex(LegacyIR):
    def execute(self, vm: LegacyVM):
        ir = self._ir
        assert isinstance(ir, Index)
        lvar = vm.get_variable(ir.variable_left)
        rvar = vm.get_variable(ir.variable_right)
        vm.set_variable(ir.lvalue, z3.Select(lvar, rvar))

class LegacyInternalCall(LegacyIR):
    def __init__(self, _ir, _chain):
        super().__init__(_ir)
        self._chain = _chain

    def execute(self, vm: LegacyVM):
        ir = self._ir
        assert isinstance(ir, InternalCall)
        if ir.lvalue:
            vm.fresh_variable(ir.lvalue)
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
        # Imply precondition
        precondition = z3.substitute(call_vm.precondition, *substitutions)
        if check_sat(z3.Not(z3.Implies(vm.constraints, precondition))):
            vm.rev = str(ir.function.nodes[1])
            return
        # Read postcondition
        for i in ir.function.nodes[2].irs:
            self._chain.add_ir(i)
        self._chain.run_chain(call_vm)
        # Handle old_
        for old_var, tmp_var in call_vm.substitutions:
            assert str(old_var).startswith('old_')
            assert str(tmp_var).startswith('c!')
            new_var = z3.Const(str(old_var)[4:], old_var.sort())
            vm.substitute(new_var, tmp_var)
        # Add postcondition
        postcondition = z3.substitute(call_vm.postcondition, *substitutions)
        vm.add_constraint(postcondition)