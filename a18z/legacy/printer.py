import z3

def pp(expr):
    operands = expr.children()
    if z3.is_and(expr):
        if len(operands) == 1:
            return pp(operands[0])
        return ' && '.join([f'{pp(x)}' for x in operands])
    elif z3.is_or(expr):
        if len(operands) == 1:
            return pp(operands[0])
        return ' || '.join([f'{pp(x)}' for x in operands])
    elif z3.is_not(expr):
        return ' ! '.join([pp(x) for x in operands])
    elif z3.is_eq(expr):
        return ' == '.join([pp(x) for x in operands])
    elif z3.is_distinct(expr):
        return ' != '.join([pp(x) for x in operands])
    elif z3.is_le(expr):
        return ' <= '.join([pp(x) for x in operands])
    elif z3.is_ge(expr):
        return ' >= '.join([pp(x) for x in operands])
    elif z3.is_add(expr):
        return ' + '.join([pp(x) for x in operands])
    elif z3.is_mul(expr):
        return ' * '.join([pp(x) for x in operands])
    elif z3.is_select(expr):
        l, r = expr.children()
        if str(l).startswith('old_'):
            name = str(l)[4:]
            return f'old({name}[{pp(r)}])'
        return f'{pp(l)}[{pp(r)}]'
    elif z3.is_store(expr):
        return '*'
    elif z3.is_const(expr):
        if str(expr) == 'True': return 'true'
        if str(expr) == 'False': return 'false'
        if str(expr).startswith('old_'): return f'old({str(expr)[4:]})'
        return str(expr)
    else:
        raise ValueError(expr)
