from slither.slithir.operations import (
    Binary,
    Assignment,
)
from .ir import (
    LegacyBinary,
    LegacyAssignment,
)

class LegacyChain:
    def __init__(self) -> None:
        self._irs = []

    def add_binary(self, ir: Binary):
        self._irs.append(LegacyBinary(ir))

    def add_assignment(self, ir: Assignment):
        self._irs.append(LegacyAssignment(ir))

    def add_ir(self, ir):
        if isinstance(ir, Binary):
            self.add_binary(ir)
        elif isinstance(ir, Assignment):
            self.add_assignment(ir)
        else: raise ValueError(ir)

    def run_chain(self, vm): 
        for ir in self._irs:
            ir.execute(vm)