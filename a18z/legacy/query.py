from slither.core.declarations import FunctionContract
from .printer import pp
from colorist import Color

class LegacyQuery:
    def __init__(self) -> None:
        self._preconditions = {}
        self._postconditions = {}

    @property
    def preconditions(self):
        return self._preconditions

    @property
    def postconditions(self):
        return self._postconditions

    def add_precondition(self, function: FunctionContract, precondition):
        name = function.canonical_name
        self._preconditions[name] = precondition

    def add_postcondition(self, function: FunctionContract, postcondition):
        name = function.canonical_name
        self._postconditions[name] = postcondition

    def get_precondition(self, function: FunctionContract):
        name = function.canonical_name
        return self._preconditions.get(name)

    def get_postcondition(self, function: FunctionContract):
        name = function.canonical_name
        return self._postconditions.get(name)

    def __copy__(self) -> 'LegacyQuery':
        r = LegacyQuery()
        r._preconditions = self._preconditions.copy()
        r._postconditions = self._postconditions.copy()
        return r

    def __str__(self) -> str:
        results = []
        for k, v in self._preconditions.items():
            results.append(f'> Pre of `{k}` is {Color.YELLOW}{pp(v)}{Color.OFF}')
        for k, v in self._postconditions.items():
            results.append(f'> Post of `{k}` is {Color.YELLOW}{pp(v)}{Color.OFF}')
        return '\n'.join(results)