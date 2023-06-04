from ..legacy import LegacyChain
from slither.slithir.operations import SolidityCall
from .ir import RevampSolidityCall

class RevampChain(LegacyChain):
    def add_solidity_call(self, ir: SolidityCall):
        self._irs.append(RevampSolidityCall(ir))