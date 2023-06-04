from slither.slithir.operations import (
    Binary,
    Assignment,
    Condition,
    Unary,
    Index,
    InternalCall
)
from slither.slithir.operations.event_call import EventCall
from slither.slithir.operations.return_operation import Return
from .ir import (
    LegacyBinary,
    LegacyAssignment,
    LegacyCondition,
    LegacyUnary,
    LegacyIndex,
    LegacyInternalCall,
    LegacyReturn,
)

class LegacyChain:
    def __init__(self) -> None:
        self._irs = []

    def add_binary(self, ir: Binary):
        self._irs.append(LegacyBinary(ir))

    def add_assignment(self, ir: Assignment):
        self._irs.append(LegacyAssignment(ir))

    def add_condition(self, ir: Condition):
        self._irs.append(LegacyCondition(ir))

    def add_unary(self, ir: Unary):
        self._irs.append(LegacyUnary(ir))

    def add_index(self, ir: Index):
        self._irs.append(LegacyIndex(ir))

    def add_internal_call(self, ir: InternalCall):
        self._irs.append(LegacyInternalCall(ir, LegacyChain()))

    def add_return(self, ir: Return):
        self._irs.append(LegacyReturn(ir))

    def add_event_call(self, ir: EventCall):
        pass

    def add_ir(self, ir):
        if isinstance(ir, Binary):
            self.add_binary(ir)
        elif isinstance(ir, Assignment):
            self.add_assignment(ir)
        elif isinstance(ir, Condition):
            self.add_condition(ir)
        elif isinstance(ir, Unary):
            self.add_unary(ir)
        elif isinstance(ir, Index):
            self.add_index(ir)
        elif isinstance(ir, InternalCall):
            self.add_internal_call(ir)
        elif isinstance(ir, Return):
            self.add_return(ir)
        elif isinstance(ir, EventCall):
            self.add_event_call(ir)
        else: raise ValueError(type(ir))

    def run_chain(self, vm): 
        for ir in self._irs:
            ir.execute(vm)
            if vm.rev: break
        # Clear all executed irs
        self._irs = []