from slither.slithir.operations import (
    Binary,
    Assignment,
    Condition,
    Unary,
    Index,
    InternalCall,
    SolidityCall,
    EventCall,
    Return,
    Transfer,
    TypeConversion,
    LibraryCall,
    Send,
    NewContract,
    Unpack
)
from slither.slithir.operations.high_level_call import HighLevelCall
from .ir import (
    LegacyBinary,
    LegacyAssignment,
    LegacyCondition,
    LegacyUnary,
    LegacyIndex,
    LegacyInternalCall,
    LegacyReturn,
    LegacySolidityCall,
    LegacyTransfer,
    LegacyTypeConversion,
    LegacyHighLevelCall,
    LegacySend,
    LegacyNewContract,
    LegacyUnpack
)
from .query import LegacyQuery

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

    def add_solidity_call(self, ir: SolidityCall):
        self._irs.append(LegacySolidityCall(ir))

    def add_transfer(self, ir: Transfer):
        self._irs.append(LegacyTransfer(ir))

    def add_type_conversion(self, ir: TypeConversion):
        self._irs.append(LegacyTypeConversion(ir))

    def add_library_call(self, ir: LibraryCall):
        self._irs.append(LegacyInternalCall(ir, LegacyChain()))

    def add_high_level_call(self, ir: HighLevelCall):
        self._irs.append(LegacyHighLevelCall(ir, LegacyChain()))

    def add_send(self, ir: Send):
        self._irs.append(LegacySend(ir))

    def add_new_contract(self, ir: NewContract):
        self._irs.append(LegacyNewContract(ir))

    def add_unpack(self, ir: Unpack):
        self._irs.append(LegacyUnpack(ir))

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
        elif isinstance(ir, SolidityCall):
            self.add_solidity_call(ir)
        elif isinstance(ir, Transfer):
            self.add_transfer(ir)
        elif isinstance(ir, TypeConversion):
            self.add_type_conversion(ir)
        elif isinstance(ir, LibraryCall):
            self.add_library_call(ir)
        elif isinstance(ir, HighLevelCall):
            self.add_high_level_call(ir)
        elif isinstance(ir, Send):
            self.add_send(ir)
        elif isinstance(ir, NewContract):
            self.add_new_contract(ir)
        elif isinstance(ir, Unpack):
            self.add_unpack(ir)
        else: raise ValueError(type(ir))

    def run_chain(self, vm, query: LegacyQuery): 
        for ir in self._irs:
            ir.execute(vm, query)
            if vm.rev: break
        self._irs = []