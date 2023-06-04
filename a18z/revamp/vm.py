import z3
from ..legacy import LegacyVM
from .utils import find_fact

class RevampVM(LegacyVM):
    def __init__(self) -> None:
        super().__init__()
        self._facts = []

    @property
    def facts(self):
        return z3.simplify(z3.And(self._facts))

    def add_fact(self, fact):
        self._facts.append(fact)

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
        self._facts.append(fact)