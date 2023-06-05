from ..legacy.vm import LegacyVM
from slither.slithir.operations import InternalCall

class PrepVM(LegacyVM):
    def __init__(self, _internal_call: InternalCall) -> None:
        super().__init__()
        self._internal_call = _internal_call

    @property
    def internal_call(self):
        return self._internal_call