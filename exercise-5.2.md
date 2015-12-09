**Exercise 5.2** Analyze the complexity of remainder_nonnegative.

Since T is an Archimedean monoid, there exists some n in QuotientType(T) such that 0 <= a - nb < b.  We will consider the time complexity in terms of n.

First consider the base case n = 0.  In this case remainder_nonnegative will return immediately.

Next, suppose n > 0.

If n is even, then we can write n = 2k, and a - nb = a - 2kb = a - k(2b), so the result of the recursive call will be the result of the entire procedure.  In particular, in this case we perform one subtraction (to check that a - b >= b), one addition (to compute the second argument b + b to the recursive call) and one recursive call on a subproblem of size n/2.

If n is odd, then we can write n = 2k + 1, and a - nb = a - (2k + 1)b = a - k(2b) - b.  In particular, we perform one subtraction, one addition, one recursive call on a subproblem of size (n-1)/2, and an additional subtraction (since b <= a - k(2b) < 2b after the recursive call returns).

The number of times n is even during some call to remainder_nonnegative is given by the number of zeros in the binary representation of n.  Similarly, the number of times n is odd is given by the number of ones in the binary representation of n.  Taking b = (floor(lg(n)) + 1) and o to be the number of ones in the binary representation of n, we conclude that the procedure performs b additions and (b + o) subtractions.  In particular, T(n) = O(lg(n)).
