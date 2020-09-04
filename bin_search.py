import z3

def binary_search(solver, lower, upper, test_var):
    """
    Searches for the largest number T between lower and upper that yields a satisfiable solution when test_var == T is added.

    Arguments:
    solver      - An instance of z3.Solver. Should have test conditions already added.
    lower       - The lower bound for the binary search.
    upper       - The upper bound for the binary search.
    test_var    - The variable to be maximised.

    Example:
    # Want to maximize the Integer X subject to X < Y == 50
    >>> X = z3.Int('x')
    >>> Y = z3.Int('y')
    >>> solver = z3.Solver()
    >>> solver.add([Y==50, X < Y])
    >>> soln, model = binary_search(solver, 10, 100, X)
    >>> soln == 49
    True
    >>> model.evaluate(X)
    49

    If the lower bound is not satisfiable returns None, None.

    To search for the smallest number simply negate all arguments and switch upper and lower.
    """

    test = None
    model = None
    solver.push()
    solver.add(test_var == lower)
    if solver.check() == z3.unsat:
        return None, None
    while(lower + 1 < upper):
        solver.pop()
        solver.push()
        test = (upper - lower) // 2 + lower
        solver.add(test_var == test)
        if (solver.check() == z3.sat):
            model = solver.model()
            lower = test
        else:
            upper = test
    return lower, model