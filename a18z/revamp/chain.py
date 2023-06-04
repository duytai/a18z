from ..legacy import LegacyChain
from slither.slithir.operations import (
    SolidityCall,
    InternalCall
)
from .ir import (
    RevampSolidityCall,
    RevampInternalCall
)

class RevampChain(LegacyChain):
    def add_solidity_call(self, ir: SolidityCall):
        self._irs.append(RevampSolidityCall(ir))

    def add_internal_call(self, ir: InternalCall):
        self._irs.append(RevampInternalCall(ir, LegacyChain()))