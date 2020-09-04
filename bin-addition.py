# Sets up a logical circuit for addition of two 8-bit unsigned integers for the z3 solver to solve. We use capitals to represent vector variables and lowercase for scalars.
# Bits are in little endian order so the number 3 is represented as 11000000. This is done so that bit i represents the number 2^i.
from z3 import BoolVector, Bool, And, Implies, Or, Not, Solver

# Summands
X = BoolVector('X', 8)
Y = BoolVector('Y', 8)
# Carry
C = BoolVector('C', 8)
# Overflow indicator
o = Bool('overflow')
# Result
R = BoolVector('R', 8)

def Equivalent(A, B):
    return And(Implies(A,B), Implies(B,A))

conditions = []

# The first bit of the carry is always zero.
conditions += [Not(C[0])]
# C_(i+1) is true iff at least two of the three of X_i, Y_i, and C_i are true
conditions += [
    (Equivalent(C[i+1],
        Or(
            And(C[i], X[i]),
            And(C[i], Y[i]),
            And(X[i], Y[i])
    )))
    for i in range(7) ]
# Overflow bit depends on last bits of X, Y, and C
conditions += [(Equivalent(o, Or(
            And(C[7], X[7]),
            And(C[7], Y[7]),
            And(X[7], Y[7]))))]

# R_i is true if an odd number of X_i, Y_i, and C_i are true
conditions += [ 
    (
        Equivalent(C[i], 
        Equivalent(X[i], 
        Equivalent(Y[i], 
                   R[i]
    )))) 
    for i in range(8) ]

# Get two numbers from the user
x_in = 1000
while x_in > 255 or x_in < 0:
    x_in = int(input("X: "))

y_in = 1000
while y_in > 255 or y_in < 0:
    y_in = int(input("Y: "))

for i in range(8):
    if (x_in >> i)&1:
        conditions.append(X[i])
    else:
        conditions.append(Not(X[i]))
    
    if (y_in >> i)&1:
        conditions.append(Y[i])
    else:
        conditions.append(Not(Y[i]))

solver = Solver()
solver.add(conditions)
solver.check()
m = solver.model()

result_out = 0
# carry_out = 0

print('R:', [m.evaluate(R[i]) for i in range(8)])
print('C:', [m.evaluate(C[i]) for i in range(8)])
for i in range(8):
    result_out += (bool( m.evaluate(R[i]) ) * (2**i))

print(f"Sum: {result_out}")
if bool(m.evaluate(o)):
    print(f"Overflow detected!")


