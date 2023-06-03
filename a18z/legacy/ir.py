from slither.slithir.operations import (
    Binary,
    Assignment,
    BinaryType
)
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
            vm.set_variable(ir.lvalue, lvar - rvar)
        elif ir.type == BinaryType.ADDITION:
            vm.set_variable(ir.lvalue, lvar + rvar)
        elif ir.type == BinaryType.EQUAL:
            vm.set_variable(ir.lvalue, lvar == rvar)
        elif ir.type == BinaryType.GREATER_EQUAL:
            vm.set_variable(ir.lvalue, lvar >= rvar)
        else: raise ValueError(ir.type)

class LegacyAssignment(LegacyIR):
    def execute(self, vm: LegacyVM):
        ir = self._ir
        assert isinstance(ir, Assignment)
        lvar = vm.get_variable(ir.lvalue)
        vm.substitute(lvar)
        rvar = vm.get_variable(ir.rvalue)
        if str(lvar) == '__v1':
            vm.add_constraint(rvar)
        elif str(lvar) == '__v2':
            vm.set_postcondition(rvar)
        else:
            vm.add_constraint(lvar == rvar)