Ignoring constant work done outside of loops:

distance:

    d + 1 comparisons       (x != y)
    d applications of f     (x = f(x))

collision_point:

    n + 1 comparisons       while (fast != slow)
    2n applications of p    if (!p(fast))
    3n applications of f    slow = f(slow);
                            fast = f(fast);
                            fast = f(fast);

collision_point_nonterminating_orbit:

    n + 1 comparisons       while (fast != slow)
    3n applications of f    slow = f(slow);
                            fast = f(fast);
                            fast = f(fast);

convergent_point:

    n + 1 comparisons       while (x0 != x1)
    2n applications of f    x0 = f(x0);
                            x1 = f(x1);

connection_point:

    n + 1 comparisons       collision_point
    2n applications of p    collision_point
    3n applications of f    collision_point

    h + 1 comparisons       convergent_point
    2h applications of f    convergent_point

connection_point_nonterminating_orbit:

    n + 1 comparisons       collision_point
    3n applications of f    collision_point

    h + 1 comparisons       convergent_point
    2h applications of f    convergent_point

orbit_structure:

    n + 1 comparisons       connection_point
    2n applications of p    connection_point
    3n applications of f    connection_point

    h + 1 comparisons       connection_point
    2h applications of f    connection_point

    h + 1 comparisons       distance(x, y, f)
    h applications of f     distance(x, y, f)

    c comparisons           distance(f(y), y, f)
    c - 1 applications of f distance(f(y), y, f)

orbit_structure_nonterminating_orbit:

    n + 1 comparisons       connection_point
    3n applications of f    connection_point

    h + 1 comparisons       connection_point
    2h applications of f    connection_point

    h + 1 comparisons       distance(x, y, f)
    h applications of f     distance(x, y, f)

    c comparisons           distance(f(y), y, f)
    c - 1 applications of f distance(f(y), y, f)

