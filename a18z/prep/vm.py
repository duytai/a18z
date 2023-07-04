import z3
from ..legacy.vm import LegacyVM
from ..pre.utils import find_fact
from slither.slithir.operations import InternalCall

class PrepVM(LegacyVM):
    def __init__(self, _internal_call: InternalCall) -> None:
        super().__init__()
        self._internal_call = _internal_call
        self._prep = []
        self._prep_substitutions = []

    @property
    def internal_call(self):
        return self._internal_call

    @property
    def prep(self):
        return self._prep

    @property
    def prep_substitutions(self):
        return self._prep_substitutions

    def add_prep(self, value):
        self._prep.append(value)

    def add_prep_substitution(self, sub):
        self._prep_substitutions.append(sub)

    def finalize(self, function=None):
        if not self.rev and self.prep :
            # Find eliminated variables
            ir = self._internal_call
            constraints = self.constraints
            postcondition = self._postcondition

            # Find all variables
            variables = z3.z3util.get_vars(z3.Implies(constraints, postcondition))

            # Find eliminated variables
            state_vars = [x.name for x in ir.function.state_variables_read]
            curr_state_vars = [x.name for x in ir.node.function.state_variables_read]
            eliminated_state_vars = list(set(curr_state_vars) - set(state_vars))

            curr_local_vars = [x.name for x in ir.node.function.local_variables]
            curr_param_vars = [x.name for x in ir.node.function.parameters]
            marker_vars = [str(x) for x in dict(self._prep_substitutions).keys()]
            curr_temp_vars = [str(x) for x in variables if str(x).startswith('c!')]
            eliminated_vars = curr_local_vars + curr_temp_vars + curr_param_vars + eliminated_state_vars
            eliminated_vars = [x for x in variables if str(x) in eliminated_vars and str(x) not in marker_vars]

            fact = find_fact(constraints, postcondition, eliminated_vars)
            if fact is not None:
                fact = z3.substitute(fact, self._prep_substitutions)
                self._prep.append(fact)
            else:
                self._prep = None
        else:
            self._prep = None