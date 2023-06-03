from slither.slithir.operations import (
    Binary,
    Assignment,
    Condition,
    Unary,
)
from .ir import (
    LegacyBinary,
    LegacyAssignment,
    LegacyCondition,
    LegacyUnary,
)

class LegacyChain:
    def __init__(self) -> None:
        self._irs = []

    def add_binary(self, ir: Binary):
        self._irs.append(LegacyBinary(ir))

    def add_assignment(self, ir: Assignment):
        self._irs.append(LegacyAssignment(ir))

    def add_condition(self, ir: Condition):
        self._irs.append(LegacyCondition(ir))

    def add_unary(self, ir: Unary):
        self._irs.append(LegacyUnary(ir))

    def add_ir(self, ir):
        if isinstance(ir, Binary):
            self.add_binary(ir)
        elif isinstance(ir, Assignment):
            self.add_assignment(ir)
        elif isinstance(ir, Condition):
            self.add_condition(ir)
        elif isinstance(ir, Unary):
            self.add_unary(ir)
        else: raise ValueError(ir)

    def run_chain(self, vm): 
        for ir in self._irs:
            ir.execute(vm)