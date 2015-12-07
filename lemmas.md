**Lemma 1.1** If a value type T is uniquely represented, equality implies representational equality.
**Proof.** Let v1, v2 be values in T such that v1 and v2 are equal.  Then v1 and v2 represent the same abstract entity x.  Since T is uniquely represented, at most one value corresponds to x; thus v1 and v2 must be the same value, and must have the same representation.  We conclude that v1 and v2 are representationally equal.

**Lemma 1.2** If a value type T is not ambiguous, representational equality implies equality.
**Proof.** Let v1, v2 be values in T with the same representation b; since T is not ambiguous, b has at most one interpretation; thus v1 and v2 must represent the same value.  We conclude that v1 and v2 are equal.

**Lemma 1.3** A well-formed object is partially formed.
**Proof.** Since any object in memory can be assigned to or destroyed, a well-formed object (which is an object in memory) can be assigned to or destroyed; thus a well-formed object is partially formed.

**Lemma 2.1**

    euclidean_norm(x, y, z) = euclidean_norm(euclidean_norm(x, y), z)

**Proof.**

    euclidean_norm(euclidean_norm(x, y), z)
        = euclidean_norm(sqrt(x * x + y * y), z)
        = sqrt(sqrt(x * x + y * y) * sqrt(x * x + y * y) + z * z)
        = sqrt(x * x + y * y + z * z)
        = euclidean_norm(x, y, z)

**Lemma 2.A** Let f be a transformation, and let n be a non-negative integer.  Then f^n is regular.
**Proof.** We will proceed by induction.

First consider the case where n = 0.  Suppose x, x' are equal; then f^0(x) = x = x' = f^0(x').

Next, consider some n > 0, and suppose the lemma is true for n - 1.  Suppose x, x' are equal.  Note that f^n(x) = f^{n-1}(f(x)) by definition; since f is regular (regularity is part of the definition of a transformation) and f^{n-1} is regular (by our inductive hypothesis), we have f(x) = f(x'), and f^{n-1}(f(x)) = f^{n-1}(f(x')), which is equal to f^n(x') by definition.  We conclude that f^n(x) = f^n(x').

**Lemma 2.B** Let f be a transformation, let x be an element in the domain of f, and let m1, m2 be non-negative integers such that f^{m1+m2}(x) is defined.  Then f^{m1+m2}(x) = f^m1(f^m2(x)).
**Proof.** We will proceed by induction.

First consider the case where m1 + m2 = 0.  Then we must have m1 = m2 = 0; thus f^{m1+m2}(x) = f^0(x) = x, and f^m1(f^m2(x)) = f^0(f^0(x)) = f^0(x) = x.

Next, consider some n > 0, and suppose the lemma is true whenever m1 + m2 < n.  Then f^{m1+m2}(x) = f^{m1+m2-1}(f(x)).  By the inductive hypothesis, the latter expression is equal to f^m1(f^{m2-1}(f(x))).  By the definition of the powers of a transformation, f^{m2-1}(f(x)) = f^m2(x).  By Lemma 2.A, f^m1 is regular, so f^m1(f^{m2-1}(f(x))) = f^m1(f^m2(x)).  We conclude that f^{m1+m2}(x) = f^m1(f^m2(x)).

**Lemma 2.C** If f^n(x) is not in the definition space of f, then f^m(x) is not defined for any integer m > n.
**Proof** We will proceed by induction.  If m = n + 1, then by Lemma 2.B we have f^m(x) = f^1(f^n(x)) = f(f^n(x)), which is not defined since f^n(x) is not in the definition space of f.  Now choose some m > n + 1, and suppose the lemma is true for m - 1.  Then again by Lemma 2.B we have f^m(x) = f^1(f^{m-1}(x)) = f(f^{m-1}(x)).  Since f^{m-1}(x) is not defined, neither is f(f^{m-1}(x)).  Since equality holds, f^m(x) cannot be defined.

**Lemma 2.2** An orbit does not contain both a cyclic and a terminal element.
**Proof.** Let O be the orbit of x under the transformation f.  Suppose O contains a cyclic element y = f^m(x), such that f^n(y) = y.  Choose any non-negative integer k, and assume that f^k(x) is a terminal element of f.  If k < m, then by Lemma 2.C f^m(x) is not defined, which contradicts that y = f^m(x).  If k >= m, we use the division algorithm to write k - m = qn + r, where r < n.  Then f^k(x) = f^{m+qn+r}(x).  By Lemmas 2.A and 2.B, the latter expression is equal to f^{r+qn}(f^m(x)) = f^{r+qn}(y).  By q additional applications of Lemmas 2.A and 2.B together with the equality f^n(y) = y, we have f^{r+qn}(y) = f^r(y).  By combining the above equalities, we have f^k(x) = f^r(y).  Using the regularity guaranteed by Lemma 2.A, f^{n-r}(f^k(x)) = f^{n-r}(f^r(y)), and applying Lemma 2.B one more time, we have f^{n-r}(f^r(y)) = f^n(y) = y.  But then f^{n-r}(f^k(x)) is defined even though f^k(x) is not in the definition space of f, which contradicts Lemma 2.C.  Thus f^k(x) is not a terminal element of f.  Since k was arbitrary, we conclude that O cannot contain both a cyclic element and a terminal element.

**Lemma 2.3** An orbit contains at most one terminal element.
**Proof.** Suppose f^m(x) and f^n(x) are distinct terminal elements of a transformation f in the orbit of x, and assume without loss of generality that m < n.  Then f^m(x) is not in the definition space of f, but f^n(x) is defined, which contradicts Lemma 2.C.  Since f and x were arbitrary, we conclude that an orbit contains at most one terminal element.

**Lemma 2.D** Let f be a transformation with domain T, and let x, y be distinct elements of T such that y is reachable from x under f.  If an object of type T occupies k bits, then the distance from x to y is at most 2^k - 1.
**Proof.** Let d be the distance from x to y.  Suppose d > 2^k - 1; then there are more than 2^k terms in the sequence x = f^0(x), f(x), ..., f^d(x) = y.  An object that occupies k bits can take at most 2^k distinct values, so by the pigeonhole principle f^i(x) = f^j(x) for some 0 <= i < j <= d.  But this contradicts Lemma 2.G; thus we conlude that d is at most 2^k - 1.

**Lemma 2.E** If the orbit of x under f has no cyclic or terminal elements, then there are infinitely many elements in the orbit.
**Proof.** Let n be a non-negative integer.  Since the orbit has no terminal elements, f^n(x) is in the definition space of f.  Since the orbit has no cyclic elements, f(f^n(x)) is distinct from x, f(x), ..., f^n(x) (if f(f^n(x)) = f^i(x) for some 0 <= i <= n, then Lemma 2.B would imply that f^{n+1-i}(f^i(x)) = f^i(x), i.e. f^i(x) is a cyclic element).  In particular, the orbit has at least n + 1 elements.  Since n was arbitrary, we conclude that the orbit has infinitely many elements.

**Lemma 2.4** o = h + c
**Proof.** Since the orbit handle is defined as the complement of the orbit cycle with respect to the orbit, the orbit handle and the orbit cycle are disjoint sets whose union is the orbit cycle.  Thus O = H U C, and the lemma follows immediately by taking the cardinality on both sides of the equation and using the fact that |A U B| = |A| + |B| for disjoint finite sets A and B.

**Lemma 2.F** If f^m(x) is cyclic, with f^k(f^m(x)) = f^m(x), then for any integer n > m, f^n(x) is also cyclic, with f^k(f^n(x)) = f^n(x).
**Proof.** Suppose f^m(x) is cyclic, i.e. f^k(f^m(x)) = f^m(x) for some positive integer k.  Then by Lemmas 2.A and 2.B, f^k(f^n(x)) = f^{k+(n-m)+m}(x) = f^{n-m}(f^k(f^m(x))) = f^{n-m}(f^m(x)) = f^n(x), and the proof is complete.

**Lemma 2.5** Let O be the orbit of x under f.  The distance from any point y1 in O to a point y2 in the cycle of O is always defined.
**Proof.** Since the integers are well-ordered and the set of integers n such that f^n(y1) = y2 is bounded below by n = 0, showing that the distance is defined reduces to showing that there exists some integer n for which f^n(y1) = y2.

Write y1 = f^m1(x), y2 = f^m2(x), and consider the following cases:
  1. If m1 and m2 are equal, then y1 = y2, and f^0(y1) = y2.
  2. If m1 is less than m2, then by Lemmas 2.A and 2.B, f^{m2-m1}(y1) = y2.
  3. If m1 is greater than m2, then by Lemma 2.F, m1 is cyclic; furthermore, if f^k(y2) = y2, then f^k(y1) = y1.  Write m1 - m2 = qk + r, where r is less than k; then by Lemma 2.D, f^{k-r}(y1) = f^{k-r}(f^m1(x)) = f^{k-r+m1-m2+m2}(x) = f^{k-r+qk+r+m2}(d) = f^{(q+1)k}(f^m2(x)) = f^m2(x) = y2.

In every possible case we've found an integer n for which f^n(y1) = y2; thus in every possible case the distance from y1 to y2 is defined.

**Lemma 2.G** If d is the distance from x to y under f, then x, f(x), ..., f^d(x) = y are all distinct.
**Proof.** Suppose f^i(x) = f^j(x) for some 0 <= i < j <= d.  Then by Lemma 2.B, f^{j-i}(f^i(x)) = f^i(x).  Using the division algorithm, we can write d - i = q(j - i) + r, where r < j - i.  Then by repeated application of Lemmas 2.A and 2.B, f^d(x) = f^{d-i+i}(x) = f^{q(j-i)+r+i}(x) = f^r(f^{q(j-1)}(f^i(x))) = f^r(f^i(x)) = f^{r+i}(x).  Since r < j - i, r + i < j <= d, which contradicts that d is the distance from x to y under f.  We conclude that x, f(x), ..., f^d(x) = y are all distinct.

**Lemma 2.6** If x and y are distinct points in an orbit cycle of size c under a transformation f, then

    c = distance(x, y, f) + distance(y, x, f)

**Proof.** Let d1 = distance(x, y, f) and let d2 = distance(y, x, f).  We will begin by showing that c is at least d1 + d2.

By Lemma 2.F, the elements f(x), ... f^d1(x) = y, ..., f^{d1+d2}(x) = x are all cyclic.  By Lemma 2.G, the elements f(x), ..., f^d1(x) = y are all distinct.  Again by Lemma 2.G, the elements f(y), ..., f^d2(y) = x are all distinct.  It remains to show that the elements f(x), ..., f^d1(x) are all distinct from the elements f(y), ..., f^d2(y).  Suppose f^i(x) = f^j(y) where 1 <= i <= d1 and 1 <= j <= d2.  Consider the following cases:
  1. If i = d1, then y = f^d1(x) = f^j(y); thus by Lemmas 2.A and 2.B, f^{d2-j}(y) = f^{d2-j}(f^j(y)) = f^d2(y) = x, which contradicts that d2 = distance(y, x, f).
  2. If j = d2, then x = f^d2(y) = f^i(x); thus by Lemmas 2.A and 2.B, f^{d1-i}(x) = f^{d1-i}(f^i(x)) = f^d1(x) = y, which contradicts that d1 = distance(x, y, f).
  3. Otherwise, y does not appear among f^k(x) for k = 1, 2, ..., i + d2 - j (for k = 1, 2, ..., i, f^k(x) = y would contradict that d1 = distance(x, y, f), and for k = i + 1, ..., i + d2 - j, f^k(x) = y would contradict that the elements y, f(y), ..., f^d2(y) are all distinct since f^k(x) = f^{k-i+j}(y), and k - i + j is between 1 + j and d2).  But by Lemmas 2.A and 2.B, f^{i+d2-j}(x) = f^{d2-j}(f^i(x)) = f^{d2-j}(f^j(y)) = f^d2{y} = x.  Now let m be any non-negative integer.  If m is less than or equal to i + d2 - j, then we have already shown that f^m(x) != y.  If m is greater than i + d2 - j, then use the division algorithm to write m = q(i + d2 - j) + r, where r is less than i + d2 - j, and by Lemmas 2.A and 2.B, f^m(x) = f^r(f^{q(i+d2-j)}(x)) = f^r(x), and f^r(x) != y.  Since m was arbitrarily, it follows that y is not reachable from x, which contradicts that d(x, y, f) = d1.

In every case we have derived a contradiction; thus f(x), ..., f^d1(x), f(y), ..., f^d2(y) are all distinct, and that c is at least d1 + d2.

To show that c is at most d1 + d2, let z be any element in the same orbit cycle as x and y.  By Lemma 2.5, z is reachable from x.  Suppose f^m(x) = z, and use the division algorithm to write m = q(d1 + d2) + r, where r < d1 + d2.  Then by Lemmas 2.A and 2.B along with the fact that f^{d1+d2}(x) = x, we have z = f^m(x) = f^{q(d1+d2)+r}(x) = f^r(x), which shows that z is among the elements f(x), ..., f^{d1+d2}(x) = x = f^0(x).  Since z was arbitrary, it follows that every element in the same orbit cycle as x and y appears among f(x), ..., f^{d1+d2}(x); thus c is at most d1 + d2.

Combining the two inequalities, it follows that c is exactly d1 + d2, and the proof is complete.

**Lemma 2.7** If x and y are points in a cycle of size c, the distance from x to y satisfies

    0 <= distance(x, y, f) < c

**Proof.** If x = y, then distance(x, y, f) = 0, which satisfies the conclusion of the lemma.  Otherwise, by Lemma 2.5, distance(y, x, f) is defined, and since x != f^0(y) = y, distance(y, x, f) > 0, so distance(x, y, f) >= c would contradict Lemma 2.6.

**Lemma 2.H** Suppose the orbit of x under the transformation f is circular or p-shaped.  Then there exists an integer n such that f^n(x) = f^{2n+1}(x).
**Proof.** Let k be the smallest integer such that f^k(x) is cyclic (such a k exists by the assumption that f is circular or p-shaped and the well-ordering property of the integers).  Let d be the distance from f^{2k+1}(x) to f^k(x) (such a d exists by Lemma 2.5).  Then by repeated application of Lemmas 2.A and 2.B,

    f^{2(k+d)+1}(x) = f^d(f^d(f^{2k+1}(x)))
                    = f^d(f^k(x))
                    = f^{k+d}(x)

Taking n = k + d gives the desired conclusion.

**Lemma 2.I** Let y be a cyclic element of the orbit O of x under the transformation f, and let k be the smallest positive integer such that f^k(y) = y.  Then k is the cycle size of O.
**Proof.** We will begin by showing that every cyclic element of O appears among y, f(y), ..., f^{k-1}(y).  Let z be any cyclic element of O.  Then by Lemma 2.5, d = distance(y, z) is defined.  If d < k, then z = f^d(y) is an element of f(y), ..., f^{k-1}(y)  If d >= k, use the division algorithm to write d = qk + r, where 0 <= r < k; then Lemma 2.A and Lemma 2.B show that z = f^d(y) = f^r(y), and z is again an element of y, f(y), ..., f^{k-1}(y).

Next, we will show that the elements y, f(y), ..., f^{k-1}(y) are distinct.  Suppose that f^i(y) = f^j(y) for some 0 <= i < j <= k - 1; then Lemma 2.A and Lemma 2.B show that f^{i+k-j} = f^{k-j}(f^i(y)) = f^{k-j}(f^j(y)) = f^k(y) = y, which contradicts that k is the smallest positive integer such that f^k(y) = y.

Finally, by Lemma 2.F, each of the elements y, f(y), ..., f^{k-1}(y) are cyclic.  We conclude that O has exactly k cyclic elements.

**Lemma 2.J** Let O be the orbit of x under the transformation f, let c be the cycle size of O, let h be the handle size of O, and let y = f^n(x) be the collision point of f and x.  Use the division algorithm to write h = mc + r, where 0 <= r < c; then the distance from y to the connection point of O is given by r + 1.
**Proof.** Use the division algorithm to write n + 1 = qc + r0, where 0 <= r0 < c.  Since f^n(x) = f^{2n+1}(x), we must have r0 = 0 (otherwise, Lemma 2.I would imply that the cycle size of O is less than c, which is a contradiction).

Next, note that n >= h (since f^n(x) is cyclic, Lemma 2.F implies that f^m(x) is cyclic for every m > n, so n < h would imply that the handle size of O is less than h, which is a contradiction).  Let d be the distance from f^{2h+1} to the cyclic element f^h(x), which exists by Lemma 2.5.  By the proof of Lemma 2.H, f^{2(h+d)+1}(x) = f^{h+d}(x); by Lemma 2.7, d < c, and by the proof of Lemma 2.I, the elements f^h(x), f^{h+1}(x), ..., f^{h+d}(x) are distinct; thus d is the smallest non-negative integer for which f^{h+d}(x) = f^{2(h+d)+1}(x), and we have n = h + d.  Now use the division algorithm to write h = mc + r, where 0 <= r < c; then by combining the equations n + 1 = qc, h = mc + r, and n = h + d, we have:

    n + 1 = qc
    h + d + 1 = qc
    mc + r + d + 1 = qc
    d + 1 = (q-m)c - r

Since 0 <= d < c and 0 <= r < c, we must have q - m = 1 (q - m < 1 would imply that d is negative, and q - m > 1 would imply that d >= c).  Thus d = c - r - 1.  Furthermore, d < c and the proof of Lemma 2.I implies that f^h(x), f^{h+1}(x), ..., f^{h+d}(x) are all distinct, and that d is the distance from the connection point f^h(x) to the collision point f^{h+d}(x).  Finally, by Lemma 2.6, we conclude that c - d = r + 1 is the distance from the collision point f^{h+d}(x) = f^n(x) to the connection point f^h(x).
