**Exercise 7.1** Would the existence of a coordinate x such that

        is_left_successor(x) ^ is_right_successor(x)

contradict the axioms of bidirectional bifurcate coordinates?

No.  We implicitly assumed (in the definition and preconditions of is_x_successor) that the first three axioms hold.  Conjunction implies disjunction, so the final axiom holds.  left y = predecessor(x); then we could have

    left_successor(y) = right_successor(y) = x

and in this case,

    predecessor(left_successor(y)) = y
    predecessor(right_successor(y)) = y

so the fourth and fifth axioms hold.
