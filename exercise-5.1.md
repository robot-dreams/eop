**Exercise 5.1** Give an example of two polynomials with integer coefficients for which slow_remainder does not terminate.

Consider the polynomials 1 and x.  We will assume that our lexicographical ordering compares higher-order terms first (so that 1 < x), though comparing lower-order terms first gives the same result.  Take a = x and b = 1 in the algorithm, and note that for any n, 1 < x - n under the given lexicographical ordering.  Thus b <= a will hold after arbitrarily many iterations of the loop, and the algorithm will never terminate.
