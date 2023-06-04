import z3

def check_sat(value):
    solver = z3.Solver()
    solver.add(value)
    return solver.check() == z3.sat

def check_unsat(value):
    solver = z3.Solver()
    solver.add(value)
    return solver.check() == z3.unsat
