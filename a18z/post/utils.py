import z3
from ..legacy.utils import check_unsat

def find_outcome(hypothesis, eliminated_vars):
    if not eliminated_vars:
        tmp_var = z3.FreshConst(z3.BoolSort())
        eliminated_vars.append(tmp_var)

    try:
        result = z3.TryFor(z3.Then(
            z3.Tactic('qe2'),
            z3.Tactic('ctx-solver-simplify'),
            z3.Tactic('ctx-simplify'),
            z3.Tactic('simplify'),
        ), 5000).apply(z3.Exists(eliminated_vars, hypothesis))

        operands = []
        for r in result[0]:
            if z3.is_eq(r):
                left, right = r.children()
                if z3.is_store(right):
                    stack = [right]
                    indexes = []
                    while stack:
                        item = stack.pop()
                        if z3.is_store(item):
                            base, index, value = item.children()
                            stack += [base, value]
                            if index not in indexes:
                                indexes.append(index)
                    expr = z3.And([left[index] == right[index] for index in indexes])
                    expr = z3.And(*z3.Then(
                        z3.With(z3.Tactic('simplify'), blast_select_store=True),
                        z3.Tactic('elim-term-ite')
                    ).apply(expr)[0])
                    variables = [x for x in z3.z3util.get_vars(expr) if str(x).startswith('k!')]
                    if variables:
                        expr = z3.And(*z3.Then(
                            z3.Tactic('qe2'),
                            z3.Tactic('ctx-solver-simplify'),
                            z3.Tactic('ctx-simplify'),
                            z3.Tactic('simplify')
                        ).apply(z3.Exists(variables, expr))[0])
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
                    expr = set([z3.And(*x) for x in split_all(expr)])
                    for r in sorted(expr, key=lambda x: -len(str(x))):
                        if check_unsat(z3.Or(expr - {r}) != z3.Or(expr)):
                            expr = expr - {r}
                    operands.append(z3.Or(expr))
                else:
                    operands.append(r)
            else:
                operands.append(r)
        return z3.simplify(z3.And(*operands))
    except:
        return None