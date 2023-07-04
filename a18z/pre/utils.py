import z3
from ..legacy.utils import check_unsat

QE2 = z3.TryFor(z3.Tactic('qe2'), 2000)

def find_fact(hypothesis, outcome, eliminated_vars):
    try:
        if not eliminated_vars:
            tmp_var = z3.FreshConst(z3.BoolSort())
            eliminated_vars.append(tmp_var)
        result = z3.Then(
            QE2,
            z3.With(z3.Tactic('simplify'), blast_select_store=True)
        ).apply(z3.ForAll(eliminated_vars, z3.Implies(hypothesis, outcome)))

        # Elimitate store(...)[x]
        old_vars = z3.z3util.get_vars(z3.And(*result[0]))
        result = z3.Tactic('elim-term-ite').apply(z3.And(*result[0]))
        new_vars = z3.z3util.get_vars(z3.And(*result[0]))
        eliminated_vars = list(set(new_vars).difference(set(old_vars)))

        if not eliminated_vars:
            tmp_var = z3.FreshConst(z3.BoolSort())
            eliminated_vars.append(tmp_var)

        # CNF form
        result = z3.Then(
            QE2,
            z3.Tactic('ctx-solver-simplify'),
            z3.Tactic('ctx-simplify'),
            z3.Tactic('simplify'),
        ).apply(z3.Exists(eliminated_vars, z3.And(*result[0])))

        # DNF form
        split_all = z3.Then(
            z3.Repeat(
                z3.OrElse(
                    z3.Tactic('split-clause'),
                    z3.Tactic('skip')
                )
            ),
            z3.Tactic('ctx-solver-simplify'),
            z3.Tactic('ctx-simplify'),
            z3.Tactic('simplify'),
        )

        # Simplify operands
        result = set([z3.And(*x) for x in split_all(z3.And(*result[0]))])
        for r in sorted(result, key=lambda x: -len(str(x))):
            if check_unsat(z3.Or(result - {r}) != z3.Or(result)):
                result = result - {r}

        # Remove contradicts
        for r in list(result):
            if check_unsat(z3.And(hypothesis, r)):
                result = result - {r}

        return z3.simplify(z3.Or(result))
    except:
        return None