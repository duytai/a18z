import z3
from ..pre import PreVM

class PreTrueVM(PreVM):
    def set_postcondition(self, value):
        self._postcondition = z3.BoolVal(True)