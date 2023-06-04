import z3
from ..legacy import LegacyVM

class RevampVM(LegacyVM):
    def set_precondition(self, value):
        self._precondition = z3.BoolVal(True)