# Question 1
# Consider the following program:
# a := 1; b := 1;
# for i := 1 to 10 do
# if ? then {a := a+2b; b := b+i} else {b := a+b; a := a+i};
# if b = 600+n then crash
# Here '?' is an unknown test that may yield false or true in any situation.
# Establish for which values of n = 1,2...,10 it is safe, that is, will not reach 'crash'.

import z3
A = z3.IntVector('A', 11)
B = z3.IntVector('B', 11)

Q = z3.BoolVector('?', 11) # Q for question mark, note Q[0] is not used at all

# Initial conditions
init_conds = [A[0] == 1, B[0] == 1]

# Iteration conditions
iter_conds = []
for i in range(1, 11):
    iter_conds += [ A[i] == z3.If(Q[i], A[i-1] + 2*B[i-1], A[i-1] + i) ]
    iter_conds += [ B[i] == z3.If(Q[i], B[i-1] + i, A[i-1] + B[i-1]) ]

conditions = init_conds + iter_conds

solver = z3.Solver()
solver.add(conditions)
solver.push()

safe = []
for n in range(1, 11):
    solver.pop()
    solver.push()
    final_condition = (B[-1] == 600 + n)
    solver.add(final_condition)
    
    if solver.check() == z3.unsat:
        # Program cannot crash
        print(f"Program cannot crash for n = {n}")
        safe.append(n)
    else:
        print(f"Program can crash for n = {n}")

print(f"Safe values of n are: {safe}")