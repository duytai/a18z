import z3
from slither.core.variables.local_variable import LocalVariable
from slither.core.variables.state_variable import StateVariable
from slither.slithir.variables.temporary import TemporaryVariable
from slither.slithir.variables.reference import ReferenceVariable
from slither.slithir.variables.constant import Constant
from .explorer import TypeExplorer, TypeState
from .utils import check_unsat

class LegacyVM:
    def __init__(self) -> None:
        self._constraints = []
        self._variables = {}
        self._substitutions = []
        self._postcondition = None

    def substitute(self, lvar):
        old_lvar = z3.FreshConst(lvar.sort())
        for variable in self._variables:
            self._variables[variable] = z3.substitute(self._variables[variable], (lvar, old_lvar))
        self._constraints = [z3.substitute(x, (lvar, old_lvar)) for x in self._constraints]
        self._substitutions.append((lvar, old_lvar))
        return old_lvar

    def add_constraint(self, constraint):
        self._constraints.append(constraint)

    def get_variable(self, variable):
        if isinstance(variable, LocalVariable):
            state = TypeState()
            TypeExplorer(variable.type, state)
            return z3.Const(variable.name, state.convert())
        elif isinstance(variable, StateVariable):
            state = TypeState()
            TypeExplorer(variable.type, state)
            return z3.Const(variable.name, state.convert())
        elif isinstance(variable, TemporaryVariable):
            return self._variables[variable]
        elif isinstance(variable, ReferenceVariable):
            return self._variables[variable]
        elif isinstance(variable, Constant):
            state = TypeState()
            TypeExplorer(variable.type, state)
            sort = state.convert()
            if sort == z3.IntSort():
                return z3.IntVal(variable.value)
            elif sort == z3.BoolSort():
                return z3.BoolVal(variable.value)
            else: raise ValueError(sort)
        else: raise ValueError(type(variable))

    def set_variable(self, variable, value):
        if isinstance(variable, TemporaryVariable):
            self._variables[variable] = value
        elif isinstance(variable, ReferenceVariable):
            self._variables[variable] = value
        else: raise ValueError(variable)

    def set_postcondition(self, value):
        substitutions = []
        for variable in z3.z3util.get_vars(value):
            if str(variable).startswith('old_'):
                new_variable = z3.Const(str(variable)[4:], variable.sort())
                tmp_variable = z3.FreshConst(variable.sort())
                self._constraints.append(new_variable == tmp_variable)
                substitutions.append((variable, tmp_variable))
        self._postcondition = z3.substitute(value, *substitutions)

    def is_verified(self):
        body = z3.And(self._constraints)
        post = self._postcondition
        print(body)
        print(post)
        return check_unsat(z3.Not(z3.Implies(body, post)))
