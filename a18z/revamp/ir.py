import z3
from slither.slithir.operations import SolidityCall
from slither.core.declarations.solidity_variables import SolidityFunction
from ..legacy.ir import LegacySolidityCall
from .vm import RevampVM


class RevampSolidityCall(LegacySolidityCall):
    def execute(self, vm: RevampVM):
        ir = self._ir
        assert isinstance(ir, SolidityCall)
        if ir.function == SolidityFunction('assert(bool)'):
            assertion = vm.get_variable(ir.arguments[0])
            exit(0)
        else: super().execute(vm)