from ..legacy.chain import LegacyChain
from slither.slithir.operations import InternalCall, LibraryCall
from .ir import PrepInternalCall

class PrepChain(LegacyChain):
    def add_internal_call(self, ir: InternalCall):
        self._irs.append(PrepInternalCall(ir, LegacyChain()))

    def add_library_call(self, ir: LibraryCall):
        self._irs.append(PrepInternalCall(ir, LegacyChain()))