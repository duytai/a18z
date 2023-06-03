
import z3
from slither.core.solidity_types.elementary_type import (
    ElementaryType,
    Uint
)

class TypeState:
    def __init__(self) -> None:
        self._sorts = []

    def add_sort(self, sort):
        self._sorts.append(sort)

    def convert(self):
        sort, *r = self._sorts
        if not r: return sort
        raise ValueError(r)

class TypeExplorer:
    def __init__(self, type_, state: TypeState) -> None:
        self.explore_type(type_, state)

    def explore_type(self, type_, state: TypeState):
        if isinstance(type_, ElementaryType):
            if type_.name in Uint:
                state.add_sort(z3.IntSort())
            elif type_.name == 'bool':
                state.add_sort(z3.BoolSort())
            else: raise ValueError(type_.name)
        else: raise ValueError(type_)