**Exercise 10.1**

(1) Find some f: N -> N that is both into and onto but not one-to-one.

Consider the function f(n) = floor(n / 2).  Since n / 2 is nonnegative whenever n is nonnegative and floor(x) is a nonnegative integer whenever x is a nonnegative real number, it follows that f(n) is into.  Let m be an arbitrary natural number; then f(2m) = m, which shows that f is onto.  However, f(0) = f(1) = 0 but 0 != 1, which shows that f is not one-to-one.

(2) Find some f: N -> N that is both into and one-to-one but not onto.

Consider the function f(n) = n + 1.  Whenever n is a natural number, n + 1 is also a natural number, so f is into.  Suppose f(n) = f(n'), i.e. n + 1 = n' + 1; then n = n', so f is one-to-one.  But there does not exist a natural number x such that x + 1 = 0; thus f is not onto.
