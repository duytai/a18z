import z3
from ..legacy.utils import check_unsat


def find_outcome(fact, hypothesis, eliminated_vars):
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

    # Remove useless
    result = set(result[0])
    for r in result:
        if check_unsat(z3.And(fact, z3.Not(r))):
            result = result - {r}

    return z3.simplify(z3.And(result))