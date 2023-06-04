import z3
from slither.slithir.operations import (
    Binary,
    Assignment,
    BinaryType,
    Condition,
    Unary,
    UnaryType,
    Index
)
from slither.slithir.variables.reference import ReferenceVariable
from .vm import LegacyVM

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
        vm.substitute(lvar)
        rvar = vm.get_variable(ir.rvalue)
        if str(lvar) == '__v1':
            vm.add_constraint(rvar)
        elif str(lvar) == '__v2':
            vm.set_postcondition(rvar)
        else:
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