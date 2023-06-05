from ..legacy import LegacyChain
from slither.slithir.operations import (
    SolidityCall,
    InternalCall
)
from .ir import (
    PreSolidityCall,
    PreInternalCall
)

class PreChain(LegacyChain):
    def add_solidity_call(self, ir: SolidityCall):
        self._irs.append(PreSolidityCall(ir))

    def add_internal_call(self, ir: InternalCall):
        self._irs.append(PreInternalCall(ir, LegacyChain()))