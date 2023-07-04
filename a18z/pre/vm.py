import z3
from ..legacy import LegacyVM
from .utils import find_fact

class PreVM(LegacyVM):
    def __init__(self, postcondition=None, num_paths=None) -> None:
        super().__init__(None, postcondition)
        self._facts = None
        self._num_paths = num_paths

    @property
    def facts(self):
        return self._facts

    @property
    def constraints(self):
        tmp = [x for idx, x in enumerate(self._constraints) if idx not in self._clocs]
        return z3.And(tmp)

    @property
    def postcondition(self):
        tmp = [x for idx, x in enumerate(self._constraints) if idx in self._clocs] + [self._postcondition]
        return z3.And(tmp)

    def add_cloc(self, cloc=None):
        if self._num_paths <= 1: return
        cloc = cloc if cloc else len(self._constraints)
        self._clocs.append(cloc)

    def add_fact(self, fact):
        if fact is not None:
            if self._facts is not None:
                self._facts = z3.simplify(z3.And(self._facts, fact))
            else:
                self._facts = fact

    def set_precondition(self, value):
        self._precondition = z3.BoolVal(True)

    def finalize(self, function=None):
        substitutions = []
        for x, y in dict(self.substitutions[::-1]).items():
            substitutions += [(x, y), (y, x)]

        constraints = z3.substitute(self.constraints, *substitutions)
        postcondition = z3.substitute(self.postcondition, *substitutions)

        variables = z3.z3util.get_vars(z3.And(constraints, postcondition))  
        local_vars = [x.name for x in function.local_variables]
        temporary_vars = [str(x) for x in variables if str(x).startswith('c!')]
        eliminated_vars = local_vars + temporary_vars
        eliminated_vars = [x for x in variables if str(x) in eliminated_vars]
        fact = find_fact(constraints, postcondition, eliminated_vars)
        self.add_fact(fact)