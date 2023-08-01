
import z3
from slither.core.solidity_types.elementary_type import ElementaryType, Uint 
from slither.core.solidity_types.mapping_type import MappingType
from slither.core.solidity_types.user_defined_type import UserDefinedType

class TypeState:
    def __init__(self) -> None:
        self._sorts = []

    def add_sort(self, sort):
        self._sorts.append(sort)

    def convert(self):
        num_sorts = len(self._sorts)
        assert num_sorts >= 1
        if num_sorts == 1:
            return self._sorts[0]
        elif num_sorts == 2:
            return z3.ArraySort(*self._sorts)
        elif num_sorts == 3:
            return z3.ArraySort(
                self._sorts[0],
                z3.ArraySort(*self._sorts[1:])
            )
        else: raise ValueError(num_sorts)

class TypeExplorer:
    def __init__(self, type_, state: TypeState) -> None:
        self.explore_type(type_, state)

    def explore_type(self, type_, state: TypeState):
        if isinstance(type_, ElementaryType):
            if type_.name in Uint:
                state.add_sort(z3.IntSort())
            elif type_.name == 'bool':
                state.add_sort(z3.BoolSort())
            elif type_.name == 'address':
                state.add_sort(z3.IntSort())
            elif type_.name == 'string':
                state.add_sort(z3.StringSort())
            else: raise ValueError(type_.name)
        elif isinstance(type_, MappingType):
            self.explore_type(type_.type_from, state)
            self.explore_type(type_.type_to, state)
        elif isinstance(type_, UserDefinedType):
            state.add_sort(z3.IntSort())
        elif isinstance(type_, list):
            t = z3.TupleSort()
            raise ValueError(type_)
        else: raise ValueError(type(type_))