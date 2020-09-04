# Question 1
# Ten jobs numbered from 1 to 10 have to be executed without interrupt, and satisfying the following requirements:
# • The running time of job i is i + 10, for i = 1, 2, . . . , 10.
# • Job 3 may only start if jobs 1 and 2 have been finished.
# • Job 6 may only start if jobs 2 and 4 have been finished.
# • Job 7 may only start if jobs 1, 4 and 5 have been finished.
# • Job 8 may only start if jobs 3 and 6 have been finished.
# • Job 9 may only start if jobs 6 and 7 have been finished.
# • Job 10 may only start if jobs 8 and 9 have been finished.
# What is the minimal total running time?

# Question 2
# Take all requirements from Question 1, but now additionally it is required that job 7 should not start earlier than job 8.
# What is the minimal total running time? 

# Question 3
# Take all requirements from Question 1 and Question 2, but now additionally it is required that jobs 3, 4 and 5 are never allowed to run at the same time, since they need a special equipment of which only one copy is available.
# What is the minimal total running time? 

import z3
from bin_search import binary_search

# Our labelling of jobs starts at 0 and ends at 9 so we need to subtract one
# from job numbers in the description
StartTimes = z3.IntVector('S', 10)
EndTimes = z3.IntVector('E', 10)

# Conditions for job lengths
# • The running time of job i is i + 10, for i = 1, 2, . . . , 10.
joblengths = [EndTimes[i] == StartTimes[i] + 11 + i for i in range(10)]

start_conditions=[]
# Jobs start after 0
start_conditions += [StartTimes[i] >= 0 for i in range(10)]
# • Job 3 may only start if jobs 1 and 2 have been finished.
start_conditions.append( StartTimes[3-1] >= EndTimes[1-1] )
start_conditions.append( StartTimes[3-1] >= EndTimes[2-1] )
# • Job 6 may only start if jobs 2 and 4 have been finished.
start_conditions.append( StartTimes[6-1] >= EndTimes[2-1] )
start_conditions.append( StartTimes[6-1] >= EndTimes[4-1] )

# • Job 7 may only start if jobs 1, 4 and 5 have been finished.
start_conditions.append( StartTimes[7-1] >= EndTimes[1-1] )
start_conditions.append( StartTimes[7-1] >= EndTimes[4-1] )
start_conditions.append( StartTimes[7-1] >= EndTimes[5-1] )

# • Job 8 may only start if jobs 3 and 6 have been finished.
start_conditions.append( StartTimes[8-1] >= EndTimes[3-1] )
start_conditions.append( StartTimes[8-1] >= EndTimes[6-1] )

# • Job 9 may only start if jobs 6 and 7 have been finished.
start_conditions.append( StartTimes[9-1] >= EndTimes[6-1] )
start_conditions.append( StartTimes[9-1] >= EndTimes[7-1] )

# • Job 10 may only start if jobs 8 and 9 have been finished.
start_conditions.append( StartTimes[10-1] >= EndTimes[8-1] )
start_conditions.append( StartTimes[10-1] >= EndTimes[9-1] )

# Question 2 specific: job 7 should not start earlier than job 8.
start_conditions.append( StartTimes[7-1] >= StartTimes[8-1])

# Question 3 specific: jobs 3, 4 and 5 are never allowed to run at the same time
start_conditions.append(z3.Or(
    StartTimes[3-1] >= EndTimes[4-1],
    StartTimes[4-1] >= EndTimes[3-1]
    ))
start_conditions.append(z3.Or(
    StartTimes[3-1] >= EndTimes[5-1],
    StartTimes[5-1] >= EndTimes[3-1]
    ))
start_conditions.append(z3.Or(
    StartTimes[4-1] >= EndTimes[5-1],
    StartTimes[5-1] >= EndTimes[4-1]
    ))

# Ends are less than max
maxEnd = z3.Int('max')
max_conditions = [EndTimes[i] <= maxEnd for i in range(10)]

conditions = joblengths + start_conditions + max_conditions

# What is the minimal total running time?
solver = z3.Solver()
solver.add(conditions)

lBound = 20 # Longest job takes 20 units
uBound = 200

# We want to minimize maxEnd so we will maximize -maxEnd

minlength, model = binary_search(solver, -uBound, -lBound, -maxEnd)

minlength = -minlength

print(f"Minimum time required to perform all jobs is {minlength}")
for i in range(10):
    print(f"Job {i+1} starts at {model.evaluate(StartTimes[i])} and ends at {model.evaluate(EndTimes[i])}")