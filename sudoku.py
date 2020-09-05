# Question 1
# Below you see a SUDOKU variant. (See sudoku.jpg)
# Again the numbers 1 to 9 should be filled, in such a way that each number occurs exactly once in every row, every column and every 3x3 block. But now there are no numbers given, only symbols '<' and 'o'. The symbol '<' means that the number left from it should be less than the number right from it.
# The symbol 'o' means that the two numbers on both sides are consecutive: they differ by exactly one. For border lines not containing a symbol '<' or 'o' nothing is known.
# Just like normal sudoku this puzzle has a unique solution (as was figured out by SMT solving). The goal is to find it. Doing this by hand looks quite impossible (you may try!), but solving it by SMT is much more feasible. Can you do this?
# As the answer you should give the 9 digit number formed by the lowest line.

import z3

S = [z3.IntVector(f"S_{i}", 9) for i in range(9)]

# Normal sudoku rules
# All numbers between 1 and 9
bounds = []
for i in range(9):
    bounds += [S[i][j] <= 9 for j in range(9)]
    bounds += [S[i][j] >= 1 for j in range(9)]

# Distinct numbers on each row
row_conditions = []
for i in range(9):
    row_conditions.append(z3.Distinct([s for s in S[i]]))

# Distinct numbers on each column
col_conditions = []
for j in range(9):
    col_conditions.append(z3.Distinct([S[i][j] for i in range(9)]))

# Distinct numbers in each box
box_conditions = []
for k in range(9):
    box_conditions.append(z3.Distinct([S[3*(k//3) + (l//3)][3*(k%3) + (l%3)] for l in range(9) ]))

# < symbols
lt_conditions = []
lt_conditions.append(S[1][3] < S[1][4])
lt_conditions.append(S[1][4] < S[1][5])
lt_conditions.append(S[1][5] < S[1][6])
lt_conditions.append(S[1][6] < S[1][7])
lt_conditions.append(S[1][7] < S[1][8])

lt_conditions.append(S[3][0] < S[3][1])
lt_conditions.append(S[3][1] < S[3][2])
lt_conditions.append(S[3][2] < S[3][3])
lt_conditions.append(S[3][3] < S[3][4])
lt_conditions.append(S[3][4] < S[3][5])

lt_conditions.append(S[5][3] < S[5][4])
lt_conditions.append(S[5][4] < S[5][5])
lt_conditions.append(S[5][5] < S[5][6])
lt_conditions.append(S[5][6] < S[5][7])
lt_conditions.append(S[5][7] < S[5][8])

lt_conditions.append(S[7][0] < S[7][1])
lt_conditions.append(S[7][1] < S[7][2])
lt_conditions.append(S[7][2] < S[7][3])
lt_conditions.append(S[7][3] < S[7][4])
lt_conditions.append(S[7][4] < S[7][5])

# Circle conditions
circ_conditions = []
circ_conditions.append(z3.Or(
    S[0][1] - S[0][2] == 1,
    S[0][2] - S[0][1] == 1
    ))
circ_conditions.append(z3.Or(
    S[0][3] - S[0][4] == 1,
    S[0][4] - S[0][3] == 1
    ))
circ_conditions.append(z3.Or(
    S[0][6] - S[0][7] == 1,
    S[0][7] - S[0][6] == 1
    ))
circ_conditions.append(z3.Or(
    S[0][5] - S[1][5] == 1,
    S[1][5] - S[0][5] == 1
    ))
circ_conditions.append(z3.Or(
    S[1][6] - S[2][6] == 1,
    S[2][6] - S[1][6] == 1
    ))
circ_conditions.append(z3.Or(
    S[2][1] - S[2][2] == 1,
    S[2][2] - S[2][1] == 1
    ))
circ_conditions.append(z3.Or(
    S[2][3] - S[2][4] == 1,
    S[2][4] - S[2][3] == 1
    ))
circ_conditions.append(z3.Or(
    S[2][4] - S[2][5] == 1,
    S[2][5] - S[2][4] == 1
    ))
circ_conditions.append(z3.Or(
    S[2][6] - S[3][6] == 1,
    S[3][6] - S[2][6] == 1
    ))
circ_conditions.append(z3.Or(
    S[2][8] - S[3][8] == 1,
    S[3][8] - S[2][8] == 1
    ))
circ_conditions.append(z3.Or(
    S[3][2] - S[4][2] == 1,
    S[4][2] - S[3][2] == 1
    ))
circ_conditions.append(z3.Or(
    S[3][6] - S[4][6] == 1,
    S[4][6] - S[3][6] == 1
    ))
circ_conditions.append(z3.Or(
    S[3][8] - S[4][8] == 1,
    S[4][8] - S[3][8] == 1
    ))
circ_conditions.append(z3.Or(
    S[4][0] - S[4][1] == 1,
    S[4][1] - S[4][0] == 1
    ))
circ_conditions.append(z3.Or(
    S[4][1] - S[4][2] == 1,
    S[4][2] - S[4][1] == 1
    ))
circ_conditions.append(z3.Or(
    S[4][3] - S[4][4] == 1,
    S[4][4] - S[4][3] == 1
    ))
circ_conditions.append(z3.Or(
    S[4][5] - S[4][6] == 1,
    S[4][6] - S[4][5] == 1
    ))
circ_conditions.append(z3.Or(
    S[4][7] - S[4][8] == 1,
    S[4][8] - S[4][7] == 1
    ))
circ_conditions.append(z3.Or(
    S[5][2] - S[6][2] == 1,
    S[6][2] - S[5][2] == 1
    ))
circ_conditions.append(z3.Or(
    S[5][2] - S[5][3] == 1,
    S[5][3] - S[5][2] == 1
    ))
circ_conditions.append(z3.Or(
    S[5][3] - S[6][3] == 1,
    S[6][3] - S[5][3] == 1
    ))
circ_conditions.append(z3.Or(
    S[5][5] - S[6][5] == 1,
    S[6][5] - S[5][5] == 1
    ))
circ_conditions.append(z3.Or(
    S[5][6] - S[6][6] == 1,
    S[6][6] - S[5][6] == 1
    ))
circ_conditions.append(z3.Or(
    S[6][2] - S[6][3] == 1,
    S[6][3] - S[6][2] == 1
    ))
circ_conditions.append(z3.Or(
    S[7][5] - S[7][6] == 1,
    S[7][6] - S[7][5] == 1
    ))

solver = z3.Solver()
solver.add(bounds + row_conditions + col_conditions + box_conditions + lt_conditions + circ_conditions)

if solver.check() == z3.sat:
    m = solver.model()
    for row in S:
        for num in row:
            print(m.evaluate(num), end=' ')
        print('\n', end='')