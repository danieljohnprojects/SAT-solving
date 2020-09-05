# For the sudoku question, is there a clever way to check that numbers in a row, column or block are unique? The naive way takes O(n^2) comparisons where n is the size of the row. Could also sort and check for increasing-ness (O(nlogn)).

# Disclaimer: I have now become aware of the Distinct command in z3 which accomplishes this much more compactly, albeit still likely with worse asymptotic behaviour. 

# Idea: sum up squares of numbers in the row. 
# Say we have 9 numbers, all between 1 and 9 (inclusive), sum of squares is 285. 
# Can this sum be achieved any way other than =1+4+9+...+81? 
# What if we have simultaneous equations? Eg sum = 45, sum of squares = 285, sum of cubes = 2025?
# What about if we mix in the product?
# Answers: 
# Sums of squares and cubes have multiple solutions, even simultaneous ones.
# Product by itself is not enough in this case. It would work if the entries to the rows were primes though.
# Product and sum gives another solution [1,2,4,4,4,5,7,9,9]. Tricky! The three, and the factors of the six and eight get mixed together.
# Product and sum of squares give only the desired solution!!!
# I expect there is some sort of algebraic/arithmetic geometry theorem that would tell you all of this straight away.
# I really should read that book about Groebner bases and stuff!

import z3

X = z3.IntVector('X', 9)
base_conditions  = [x >= 1 for x in X]
base_conditions += [x <= 9 for x in X]

# Without loss of generality we put the numbers in non-decreasing order
for i in range(8):
    base_conditions.append(X[i]<=X[i+1])

# Exclude the solution 1,2,3,...,9
base_conditions.append(z3.Not(z3.And([X[i] == i+1 for i in range(9)])))

# Set sum to 45
sum_cond = [z3.Sum(X) == 45]
# Set sum of squares to 285
square_conds = [ z3.Sum( [x**2 for x in X] ) == 285 ]
# Set cubes to 2025
cube_conds = [ z3.Sum( [x**3 for x in X] ) == 2025 ]

product_cond = [z3.Product(X) == 362880]

solver = z3.Solver()
solver.add(base_conditions)
# simul_poly_solver = z3.Solver()
# simul_poly_solver.add(base_conditions + sum_cond + square_conds + cube_conds)

# sum_prod_solver = z3.Solver()
# sum_prod_solver.add(base_conditions + sum_cond + product_cond)

# square_prod_solver = z3.Solver()
# square_prod_solver.add(base_conditions + sum_cond + product_cond)
additional_condtions = {
    "Sum, squares, cubes": sum_cond + square_conds + cube_conds,
    "Sum, product": sum_cond + product_cond,
    "Squares, product": square_conds + product_cond
}
for name, conds in additional_condtions.items():
    solver.push()
    solver.add(conds)
    if solver.check() == z3.sat:
        m = solver.model()
        print(name + " is satisfiable")
        print("An alternative solution is", [m.evaluate(x) for x in X])
    else:
        print(name + " is not satisfiable")
    solver.pop()
 