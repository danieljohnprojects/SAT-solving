# Eight trucks have to deliver pallets of obscure building blocks to a magic factory. Every truck has a capacity of 8000 kg and can carry at most eight pallets. In total, the following has to be delivered:

# •Four pallets of nuzzles, each of weight 800 kg.

# •A number of pallets of prittles, each of weight 1100 kg.

# •Eight pallets of skipples, each of weight 1000 kg.

# •Ten pallets of crottles, each of weight 2500 kg.

# •Twenty pallets of dupples, each of weight 200 kg.

# Skipples need to be cooled; only three of the eight trucks have the facility for cooling skipples.

# Nuzzles are very valuable; to distribute the risk of loss no two pallets of nuzzles may be in the same truck.

# Investigate what is the maximum number of pallets of prittles that can be delivered.

# (Hint: if you do not use the maximize command, you may run the tool several times and do a binary search to find the right value)

# from z3 import IntVector, Sum, Solver
import z3

N = z3.IntVector('N', 8) # Number of Nuzzle pallets on each truck
P = z3.IntVector('P', 8) # Number of Prittle pallets on each truck
S = z3.IntVector('S', 3) # Number of Skipple pallets on each refridgerated truck
C = z3.IntVector('C', 8) # Number of Crottle pallets on each truck
D = z3.IntVector('D', 8) # Number of Dupple pallets on each truck

# Weight restrictions for refridgerated trucks
weight_restriction = [ 800*N[i] + 1100*P[i] + 1000*S[i] + 2500*C[i] + 200*D[i] <= 8000 for i in range(3) ]
# Weight restrictions for non-refridgerated trucks
weight_restriction += [ 800*N[i] + 1100*P[i] + 2500*C[i] + 200*D[i] <= 8000 for i in range(3, 8) ]

# Pallet restrictions for refridgerated trucks
pallet_restriction = [ N[i] + P[i] + S[i] + C[i] + D[i] <= 8 for i in range(3) ]
pallet_restriction += [ N[i] + P[i] + C[i] + D[i] <= 8 for i in range(3,8) ]

# Only one Nuzzle pallet on each truck
nuzzle_restriction = [ N[i] <= 1 for i in range(8) ]

# Quantity restrictions
quantity_restriction = [
    z3.Sum(N) == 4,
    z3.Sum(S) == 8,
    z3.Sum(C) == 10,
    z3.Sum(D) == 20,
]
quantity_restriction += [N[i] >= 0 for i in range(8)]
quantity_restriction += [P[i] >= 0 for i in range(8)]
quantity_restriction += [S[i] >= 0 for i in range(3)]
quantity_restriction += [C[i] >= 0 for i in range(8)]
quantity_restriction += [D[i] >= 0 for i in range(8)]

# Explosive restrictions
explosive_restriction = [z3.Implies(P[i] > 0, C[i] == 0) for i in range(8)]
# explosive_restriction += [z3.Implies(C[i] > 0, P[i] == 0) for i in range(8)]

conditions = weight_restriction + pallet_restriction + nuzzle_restriction + quantity_restriction + explosive_restriction

# Perform binary search to find the maximum number of Prittle pallets
solver = z3.Solver()
solver.add(conditions)
lBound = 0
uBound = 100
testBound = 50
m = None
solver.push()

while(lBound + 1 < uBound):
    solver.pop()
    solver.push()
    testBound = ((uBound - lBound) // 2) + lBound
    solver.add(z3.Sum(P) == testBound)
    if (solver.check() == z3.sat):
        m = solver.model()
        lBound = testBound
    else:
        uBound = testBound

# solver.check()
# m = solver.model()
print(f"We can transport at most {lBound} Prittle pallets.")
print()
print("A satisfying arrangement is as follows.")
for i in range(8):
    print(f"Truck {i}:")
    print(f"{m.evaluate(P[i])} pallets of Prittles")
    print(f"{m.evaluate(N[i])} pallets of Nuzzles")
    print(f"{m.evaluate(C[i])} pallets of Crottles")
    print(f"{m.evaluate(D[i])} pallets of Dupples")
    if (i < 3):
        print(f"{m.evaluate(S[i])} pallets of Skipples")
        

