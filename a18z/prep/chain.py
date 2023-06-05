from ..legacy.chain import LegacyChain
from slither.slithir.operations import InternalCall
from .ir import PrepInternalCall

class PrepChain(LegacyChain):
    def add_internal_call(self, ir: InternalCall):
        self._irs.append(PrepInternalCall(ir, LegacyChain()))