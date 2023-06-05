import z3
from ..legacy.utils import check_unsat

def find_outcome(hypothesis, eliminated_vars):
    if not eliminated_vars:
        tmp_var = z3.FreshConst(z3.BoolSort())
        eliminated_vars.append(tmp_var)

    # CNF form
    result = z3.Then(
        z3.Tactic('qe2'),
        z3.Tactic('ctx-solver-simplify'),
        z3.Tactic('ctx-simplify'),
        z3.Tactic('simplify'),
    ).apply(z3.Exists(eliminated_vars, hypothesis))

    return z3.simplify(z3.And(*result[0]))