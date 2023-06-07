from slither.core.declarations import FunctionContract

class LegacyQuery:
    def __init__(self) -> None:
        self._pre_conditions = {}
        self._post_conditions = {}

    def add_precondition(self, function: FunctionContract, precondition):
        name = function.canonical_name
        self._pre_conditions[name] = precondition

    def add_postcondition(self, function: FunctionContract, postcondition):
        name = function.canonical_name
        self._post_conditions[name] = postcondition

    def get_precondition(self, function: FunctionContract):
        name = function.canonical_name
        return self._pre_conditions.get(name)

    def get_postcondition(self, function: FunctionContract):
        name = function.canonical_name
        return self._post_conditions.get(name)

    def __str__(self) -> str:
        results = []
        for k, v in self._pre_conditions.items():
            results.append(f'> Pre of `{k}` is {v}')
        for k, v in self._post_conditions.items():
            results.append(f'> Post of `{k}` is {v}')
        return '\n'.join(results)