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

    def add_ir(self, ir):
        if isinstance(ir, Binary):
            self._irs.append(LegacyBinary(ir))
        elif isinstance(ir, Assignment):
            self._irs.append(LegacyAssignment(ir))
        else: raise ValueError(ir)

    def run_chain(self, vm): 
        for ir in self._irs:
            ir.execute(vm)