**Exercise 1.2** Assuming that int is a 32-bit two's complement type, determine the exact definition and result space of the following functional procedure:

        int square(int n) { return n * n; }

The definition space is the closed interval of integers [-46340, 46340]; the result space is the set {x^2 | x is an integer and x is in [-46340, 46340]}, i.e. {0, 1, 4, 9, ..., 46340^2}.
