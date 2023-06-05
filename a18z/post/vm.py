import z3
from ..legacy import LegacyVM
from .utils import find_outcome

class PostVM(LegacyVM):
    def __init__(self, precondition=None, postcondition=None) -> None:
        super().__init__(precondition, postcondition)
        self._outcomes = []

    @property
    def outcomes(self):
        return z3.simplify(z3.And(self._outcomes))

    def add_outcome(self, outcome):
        self._outcomes.append(outcome)

    def set_postcondition(self, value):
        self._postcondition = z3.BoolVal(True)

    def finalize(self, function=None):
        if not self.rev:

            substitutions = []
            for x, y in dict(self.substitutions[::-1]).items():
                old_var = z3.Const(f'old_{str(x)}', x.sort())
                substitutions.append((y, old_var))
            constraints = z3.substitute(self.constraints, *substitutions)

            variables = z3.z3util.get_vars(constraints)  
            local_vars = [x.name for x in function.local_variables]
            temporary_vars = [str(x) for x in variables if str(x).startswith('c!')]
            eliminated_vars = local_vars + temporary_vars
            eliminated_vars = [x for x in variables if str(x) in eliminated_vars]

            outcome = find_outcome(constraints, eliminated_vars)
            self._outcomes.append(outcome)