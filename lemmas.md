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
    d = (q-m)c - r - 1

Since 0 <= d < c and 0 <= r < c, we must have q - m = 1 (q - m < 1 would imply that d is negative, and q - m > 1 would imply that d >= c).  Thus d = c - r - 1.  Furthermore, d < c and the proof of Lemma 2.I implies that f^h(x), f^{h+1}(x), ..., f^{h+d}(x) are all distinct, and that d is the distance from the connection point f^h(x) to the collision point f^{h+d}(x).  Finally, by Lemma 2.6, we conclude that c - d = r + 1 is the distance from the collision point f^{h+d}(x) = f^n(x) to the connection point f^h(x).

**Corollary 2.K** Let O be the orbit of x under the transformation f, and let y = f^n(x) be the collision point of f and x.  Then f(y) = x if and only if O is circular.
**Proof.** If f(y) = x, then Lemmas 2.A and 2.B imply f(f^n(x)) = f^{n+1}(x) = x; thus x is cyclic, and O is circular.  Conversely if O is circular, then h = 0 (h is the handle size of O), so r = 0 in the statement of Lemma 2.J, and by the conclusion of the lemma, the distance from y to the connection point is 1.  Since O is circular, x is the connection point of O; thus f(y) = x, and the proof is complete.

**Corollary 2.L** If c is the cycle size of O, then for any cyclic element y we have y = f^c(y).
**Proof** If y = f(y) then Lemma 2.I implies that c = 1, and there is nothing more to prove.  Otherwise, y and f(y) are distinct cyclic elements of O.  Let d be the distance from f(y) to y; then by Lemma 2.6, 1 + d = c, so we have f^c(y) = f^{d+1}(y) = f^d(f(y)) = y.

**Lemma 2.M** Let O be the orbit of x under the transformation f, let y = f^n(x) be the collision point of f and x, and let h be the handle size of O.  Then h is the smallest integer such that f^h(x) = f^h(f(y)).
**Proof.** If f^i(x) were cyclic for any i < h, then Lemma 2.F would imply that h <= i, which contradicts i < h; thus none of x, f(x), ..., f^{h-1}(x) are cyclic.  Since y is cyclic, by Lemma 2.F so are f(y), ..., f^{h-1}(f(y)).  It follows that for any i < h, we cannot have f^i(x) = f^i(f(y)) because the expression on the left is not cyclic but the expression on the right is cyclic.  It remains to show that f^h(x) = f^h(f(y)).  Write h = mc + r where c is the cycle size of O.  By Lemma 2.J, the distance from y to the connection point f^h(x) is r + 1, and by Corollary 2.L, f^c(f(y)) = f(y); thus by Lemmas 2.A and 2.B, f^h(f(y)) = f^{r+mc}(f(y)) = f^r(f(y)) = f^{r+1}(y) = f^h(x), and the proof is complete.

**Lemma 2.8** If the orbits O1 and O2 of the elements x1 and x2 under the transformation f intersect, then O1 and O2 have the same cyclic elements.
**Proof.** Let z be the intersection point of O1 and O2.  Given an arbitrary cyclic element y1 of O1, Lemma 2.5 shows that y1 is reachable from z; thus y1 is reachable from x2.  Similarly, given an arbitrary cyclic element y2 of O2, Lemma 2.5 shows that y2 is reachable from z; thus y2 is reachable from x1.  It follows that set of cyclic elements of O1 is equal to the set of cyclic elements of O2.

**Lemma 3.1** a^m a^n = a^n a^m = a^{n+m} (powers of the same element commute).
**Proof.** We consider only positive powers m and n, and we will proceed by induction on m + n.  If m + n = 2, then we must have m = n = 1, so a^m a^n, a^n a^n, and a^2 are all equivalent to a * a.  Now suppose the claim is true for m + n = k - 1, where k > 2 (in particular, either m > 1 or n > 1).  Consider the following cases:

1. If m = 1, then

        a^m a^n = a * a^n
                = a * (a^{n-1} * a)
                = (a * a^{n-1}) * a
                = a^n * a
                = a^n a^m

        a^m a^n = a * a^n
                = a^{1+n}
                = a^{m+n}

2. If n = 1, then

        a^m a^n = a^m * a
                = (a * a^{m-1}) * a
                = a * (a^{m-1} * a)
                = a * a^m
                = a^n a^m

        a^m a^n = a^m * a
                = a^{m+1}
                = a^{m+n}

3. If m > 1 and n > 1, then

        a^m a^n = (a * a^{m-1}) * (a * a^{n-1})
                = a * (a^{m-1} * a^{n-1}) * a
                = a * (a^{n-1} * a^{m-1}) * a
                = (a * a^{n-1}) * (a^{m-1} * a)
                = a^n * a^m

        a^m a^n = (a * a^{m-1}) * a^n
                = a * (a^{m-1} * a^n)
                = a * a^{m-1+n}
                = a^{m+n}

**Lemma 3.2** (a^n)^m = a^{nm}
**Proof.** We consider only positive integers m and n, and we will proceed by induction on m + n.  If m + n = 2, then we must have m = n = 1, so (a^n)^m = (a^1)^1 = a, and a^{nm} = a^{1*1} = a^1 = a.  Now suppose the claim is true for m + n = k - 1, where k > 2, and consider the following cases:

1. If m = 1, then

        (a^n)^m = a^n
                = a^{n*1}
                = a^{nm}

2. If n = 1, then

        (a^n)^m = (a^1)^m
                = a^m
                = a^{1*m}
                = a^{nm}

3. If m > 1 and n > 1, then by Lemma 3.1 and our inductive hypothesis we have

        (a^n)^m = a^n * (a^n)^{m-1}
                = a^n * a^{n(m-1)}
                = a^n * a^{nm-n}
                = a^{n+nm-n}
                = a^nm

**Lemma 3.3** The binary operation of composition is associative.
**Proof.** Let f, g, and h be transformations on T; then for any element x in T, we have

    f o (g o h)(x) = f(g o h(x))
                   = f(g(h(x)))

as well as

    (f o g) o h(x) = (f o g)(h(x))
                   = f(g(h(x)))

from which we conclude that either f o (g o h) and (f o g) o h are both undefined, or they both map x to the same element.  Since x was arbitrary, we conclude that they are the same transformation.

**Lemma 3.4** collision_point_nonterminating_orbit can be used in the proof of Theorem 3.1.
**Proof.** By Lemma 2.2, the orbit of x under f cannot contain both a cyclic element and a terminal element; since x has finite order, its orbit contains a cyclic element and no terminal elements.  In particular, f^n(x) is in the definition space of f for every non-negative integer n (otherwise f^n(x) would be a terminal element of the orbit), so p(x) will always return true in the collision_point algorithm.

**Lemma 4.1** If r is an equivalence relation, a = b implies r(a, b).
**Proof.** This follows immediately from the fact that equivalence relations are reflexive.

**Lemma 4.2** key_function(f, r) implies equivalence(r)
**Proof.** Let a, b, c be arbitrary elements in the domain of r.  Suppose r(a, b) and r(b, c); then f(a) = f(b) and f(b) = f(c).  By transitivity of equality, f(a) = f(c); then r(a, c), and r is transitive.  Next, suppose r(a, b); then f(a) = f(b).  By symmetry of equality ,f(b) = f(a); then r(b, a) and r is symmetric.  Finally, since f(a) = f(a) for any a in the domain of f (which is the same as the domain of r), we have r(a, a), i.e. r is reflexive.  We conclude that r is an equivalence relation.

**Lemma 4.3** The symmetric complement of a weak ordering is an equivalence relation.
**Proof.** Let r be a weak ordering, and let e be its associated equivalence relation.  Suppose !r(a, b) ^ !r(b, a) as well as !r(b, c) ^ !r(c, b).  Then weak-trichotomy gives e(a, b) and e(b, c), which implies e(a, c).  A second application of weak-trichtomy shows !r(a, c) ^ !r(c, a).  Next, suppose !r(a, b) ^ !r(b, a).  Since conjunction is a commutative operation, we also have !r(b, a) ^ !r(a, b).  Finally, since e(a, a) for any a in the domain of e (which is the same as the domain of r), weak-trichotomy implies that !r(a, a), and the proof is complete.

**Lemma 4.4** A total ordering is a weak ordering.
**Proof.** Take equality to be the equivalence relation in the definition of a weak ordering.

**Lemma 4.5** A weak ordering is asymmetric.
**Proof.** Having both r(a, b) and r(b, a) hold would violate weak-trichotomy.

**Lemma 4.6** A weak ordering is strict.
**Proof.** Since e(a, a) holds for any equivalence relation, having r(a, a) would violate weak-trichotomy.

**Lemma 4.7** select_2_5 performs six comparisons.
**Proof.** By direct count:

    select_2_5 performs one comparison and then calls select_2_5_ab
    select_2_5_ab performs one comparison and then calls select_2_5_ab_cd
    select_2_5_ab_cd performs one comparison and then calls select_1_4_ab
    select_1_4_ab performs one comparison and then calls select_1_4_ab_cd
    select_1_4_ab_cd performs one comparison and then calls select_0_2
    select_0_2 performs one comparison and then returns

**Lemma 5.1** An identity element is unique:

    identity_element(e, op) ^ identity_element(e', op) implies e = e'

**Proof.** Since e is an identity element, op(e, e') = e.  Since e' is an identity element, op(e, e') = e'.  Combining these two equations gives e = e'.

**Lemma 5.2** f(n) = n^3 is the multiplicative inverse for the multiplication of non-zero remainders modulo 5.
**Proof.** We simply check each case (modular multiplication is commutative, so we only need to check one direction):

    1 * 1^3 = 1 (mod 5)
    2 * 2^3 = 16 = 1 (mod 5)
    3 * 3^3 = 81 = 1 (mod 5)
    4 * 4^3 = -1 * (-1)^3 = 1 (mod 5)

**Lemma 5.A** Composition of transformations is not necessarily commutative.
**Proof.** Let f(x) = x^2 and g(x) = x + 1; then f(g(1)) = 4, but g(f(1)) = 2.

**Lemma 5.3** In an additive group, -0 = 0.
**Proof.** By defition of an inverse operation, (-0) + 0 = 0.  Since 0 is the identity element of +, it follows that (-0) + 0 = (-0).  Combining these two equations gives 0 = -0.

**Lemma 5.4** Every additive group is a module over integers with appropriately defined scalar multiplication.
**Proof.** Define scalar multiplication as follows, where a is an arbitrary element of the additive group:

    0 * a = 0 (the 0 on the left refers to the integer, the 0 on the right refers to the identity of the additive group)
    1 * a = a
    -1 * a = -a (the - on the right refers to the inverse operation of the additive group)
    For any positive integer n:

        n * a = a + ... + a (n copies)
        -n * a = (-a) + ... + (-a) (n copies)

The fact that this definition makes the additive group into a module over integers follows immediately from the associativity and commutativity properties of the additive group.

**Lemma 5.5** In an ordered additive semigroup, a < b ^ c < d implies a + c < b + d.
**Proof.** Since a < b, the definition of OrderedAdditiveSemigroup gives a + c < b + c.  Furthermore, since c < d, we also have c + b < d + b.  By regularity of type and commutativity of addition, we also have b + c < b + d.  Finally, by transitivity of <, we have a + c < b + d.

**Lemma 5.6** In an ordered additive monoid viewed as a semimodule over natural numbers, a > 0 ^ n > 0 implies na > 0.
**Proof.** We proceed by induction.  If n = 1, then na = a, and a > 0 by assumption.  Suppose a > 0 and (n-1)a > 0, where n > 1.  Then na = a + ... + a = a + (n-1)a = (n-1)a + a; by the definition of OrderedAdditiveMonoid, (n-1)a > 0 implies (n-1)a + a > 0 + a; by regularity of type and definition of additive identity, na > a; finally, by transitivity of > (since a > 0), na > 0, and the induction is complete.

**Lemma 5.7** In an ordered additive group, a < b implies -b < -a.
**Proof.** Since a < b, by the definition of OrderedAdditiveGroup, a + (-a) < b + (-a); by regularity of type and the definition of additive inverse, 0 < b + (-a).  Furthermore, another application of the definition of OrderedAdditiveGroup gives 0 + (-b) < b + (-a) + (-b).  Using the definition of additive identity on the right as well as commutativity of + and the definition of additive inverse on the left, we have -b < -a, as desired.

**Lemma 5.8** In an ordered additive group, a < 0 implies 0 < -a.
**Proof.** This follows immediately from Lemma 5.3 (-0 = 0) and Lemma 5.7 (a < b implies -b < -a).

**Lemma 5.9** Absolute value satisfies the following properties:

    |a  -  b|    =    |b  -  a|     (1)
    |a  +  b|   <=    |a| + |b|     (2)
    |a  -  b|   >=    |a| - |b|     (3)
    |a| =  0  implies  a  =  0      (4)
     a !=  0  implies |a| >  0      (5)

**Proof.**

    (1) Suppose a - b > 0.  Since a - b + b - a = 0, we have -(a - b) = b - a, and by Lemmas 5.3 and 5.7, b - a < 0.  Thus |a - b| = a - b and |b - a| = -(b - a) = a - b.  We can use a similar argument in the case of b - a > 0.  Finally, if a - b = 0, then |a - b| = -0 = 0 and |b - a| = -0 = 0.
    (2) If a and b are both positive, then |a| + |b| = a + b, and Lemma 5.5 implies a + b > 0, i.e. |a + b| = a + b.  If a and b are both zero or negative, then |a| + |b| = -a + -b, and Lemma 5.5 implies a + b <= 0, i.e. |a + b| = -(a + b) = -a + -b.  If a is positive, b is zero or negative, and a + b > 0, then |a| + |b| = a + -b, and |a + b| = a + b, and -b > b implies |a| + |b| > |a + b|.  If a is positive, b is zero or negative, and a + b <= 0, then |a| + |b| = a + -b, and |a + b| = -(a + b) = -a + -b, and a > -a implies |a| + |b| > |a + b|.  For the last two cases (the two cases where b is positive and a is zero or negative), we use a similar argument to the two cases where a is positive and b is zero or negative.
    (3) We enumerate each case, similar to the proof of (2)
    (4) Suppose |a| = 0.  Then by trichotomy, |a| > 0 does not hold, and by the contrapositive of (5), which we prove below, a != 0 does not hold.  We conclude that if |a| = 0, then a = 0.
    (5) If a > 0, then |a| = a, and there is nothing to prove.  If a < 0, then |a| = -a, and Lemma 5.8 shows that -a > 0.

**Lemma 5.10** The following are Archimedean monoids: integers, rational numbers, binary fractions {n / 2^k}, ternary fractions {n / 3^k}, and real numbers.
**Proof.**

Integers: let a >= 0, b > 0 be given.  Every step of the algorithm decreases a by at least 1; thus after a steps, we are guaranteed to have a <= 0 < b; thus b <= a will not hold, and the algorithm will terminate.

Rational numbers: Write a = a0/a1 and b = b0/b1, where a0 is nonnegative and a1, b0, b1 are all positive.  Note that a0/a1 - n * b0/b1 < b0/b1 if and only if a0 * b1 - n * b0 * a1 < b0 * a1.  Since integers are an Archimedean monoid, there exists n such that the latter holds; thus there exists n such that the former holds.

Binary fractions, ternary fractions: These are a special case of rational numbers.

Real numbers: Let a >= 0, b > 0 be given.  Let b' be any rational number between 0 and b, and let a' be any rational number greater than a (we will not prove here that such b' and a' exist).  Since rational numbers are an Archimedean monoid, we can find n such that a' - n * b' < b'.  Since b' < b, we have a' - n * b' < b; since -n * b < -n * b', we have a' - n * b < b; finally, since a < a', we have a - n * b < b.  Thus the original algorithm applied to the real numbers a and b will terminate after at most n steps.

**Lemma 5.11** The result of doubling a positive element of a halvable monoid k times may be halved k times.
**Proof.** We proceed by induction on k.  If k = 0 then there is nothing to prove.  Suppose the claim is true for k - 1, where k > 0.  Let c be the result of doubling some element b of the halvable monoid k - 1 times.  Doubling again gives an element c' = c + c.  By definition of a halvable monoid, we must have half(c') = c.  By our inductive hypothesis, we can halve c k - 1 additional times to obtain b.  Thus halving c' k times gives b, and the proof is complete.

**Lemma 5.B** Given an Archimedean monoid T and elements a >= 0, b > 0, there is a unique element n in QuotientType(T) such that 0 <= a - nb < b.
**Proof.** Since T is an Archimedean monoid, such an n exists.  Suppose n' > n; then a - n'b = a - nb - (n' - n)b <= a - nb - b, but a - nb < b implies a - nb - b < 0.  Next, suppose n' < n; then a - n'b = a - nb + (n - n')b >= a - nb + b, but a - nb >= 0 implies a - nb + b >= b.  By trichotomy of QuotientType(T), we conclude that n = n'.

**Lemma 5.12** In an Archimedean monoid T with positive x, a, b:

    (1) b divides a <=> remainder_nonnegative(a, b) = 0
    (2) b divides a implies b <= a
    (3) a > b ^ x divides a ^ x divides b implies x divides (a - b)
    (4) x divides a ^ x divides b implies x divides remainder_nonnegative(a, b)

**Proof.**

(1) Since b divides a, there exists an element n in QuotientType(T) such that a = nb, i.e. a - nb = 0.  The procedure remainder_nonnegative returns some n' in QuotientType(T) such that 0 <= a - n'b < b.  By Lemma 5.B, there is only one possible value of n' such that 0 <= a - n'b < b; thus we must have n = n'.

(2) Write a = nb.  We will proceed by induction on n.  Note that n must be positive (if n = 0 then we would have nb = 0, and if n < 0 then we would have nb < 0).  If n = 1, then a = 1 * b = b, and the claim trivially holds.  Suppose the claim is true for n - 1, where n > 1.  If a = nb, then a - b = (n - 1)b.  By the inductive hypothesis, a - b >= b.  Since b is positive, we have a > a - b >= b, and the proof is complete.

(3) If x divides a, then we can write a = nx.  If x divides b, then we can write b = mx.  By distributivity, it follows that a - b = nx - mx = (n - m)x, so x divides (a - b).

(4) First note that if x divides b, then x divides kb for any k in QuotientType(T) (if x divides b then we can write b = mx; then kb = kmx).  The procedure remainder_nonnegative returns the value a - kb for some k; since x divides a and x divides kb, by (3) x divides their difference.

**Lemma 5.13** In an Archimedean monoid, the following holds for positive x, a, b:

    (1) gcd is commutative
    (2) gcd is associative
    (3) x divides a ^ x divides b implies x <= gcd(a, b)
    (4) gcd(a, b) is unique
    (5) gcd(a, a) = a
    (6) a > b implies gcd(a, b) = gcd(a - b, b)

**Proof.**

    (1) Swapping the roles of a and b in the definition of gcd(a, b) only changes the order of conjunctions; since conjunction is commutative, so is gcd.
    (2) Let x = gcd(gcd(a, b), c).  Then (i) x divides gcd(a, b), (ii) x divides c, and (iii) if x' divides both gcd(a, b) and c, then x' divides x.  Furthermore, expanding (i) gives that x divides a and x divides b.  Let y = gcd(a, gcd(b, c)).  Then (i) y divides a, (ii) y divides gcd(b, c), and (iii) if y' divides both a and gcd(b, c), then y' divides y.  Furthermore, expanding (ii) gives that y divides b and y divides c.

    We already know that x divides a.  Since x divides b and x divides c, x divides gcd(b, c).  Thus x divides y, and x <= y.  We already know that y divides c.  Since y divides a and y divides b, y divides gcd(a, b).  Thus y divides x, and y <= x.  We conclude that x = y.

    (3) By definition of gcd(a, b), x divides a and x divides b implies that x divides gcd(a, b); Lemma 5.12(2) implies that x <= gcd(a, b).
    (4) Suppose d and d' are both greatest common divisors of a and b.  Then d divides d', so Lemma 5.12(2) implies that d <= d', and d' divides d, so Lemma 5.12(2) implies that d' <= d.  By trichotomy, we conclude that d' = d.
    (5) First, note that a divides a (a = 1 * a) and a divides a.  Next, suppose d divides a and d divides a.  Then d divides a.  Thus a satisfies the definition of gcd(a, a).

**Lemma 5.14** subtractive_gcd_nonzero always terminates for integers and rationals.
**Proof.** We start with the integer case.  Consider a single iteration of the loop.

If a = b then the procedure returns, and there is nothing to prove.  If a > b, then a - b < a and max(a, b) = a, so max(a - b, b) < max(a, b).  If b < a, then b - a < b and max(a, b) = b, so max(a, b - a) < max(a, b).  In either case, max(a, b) decreases.

Next, note that since we only set a to a - b if a > b, and we only set b to b - a if b > a, a and b are always positive.  In particular, max(a, b) is always positive.

Suppose the procedure executes more than max(a, b) iterations of the loop; since a single iteration of the loop decreases max(a, b) by 1, max(a, b) would become negative, which is a contradiction.  We conclude that the procedure must terminate after no more than max(a, b) iterations of the loop.

Next, we consider the rational case.  Note that multiplication by a positive integer preserves the order of rationals; in particular, if a < b then ka < kb.  Furthermore, if c = a - b, then kc = ka - kb.  Thus the procedure will perform precisely the same number of iterations if we multiply both of its arguments by the same positive integer.  Let a = a0/a1 and b = b0/b1 be the original arguments; then applying the procedure with a' = a0 * b1 and b' = b0 * a1 will perform the same number of iterations, but since a' and b' are integers, our proof for the integer case shows that the rational case also terminates.

**Lemma 5.15** gcd(a / gcd(a, b), b / gcd(a, b)) = 1.
**Proof.** Suppose d divides a / gcd(a, b) and b / gcd(a, b).  Then d * gcd(a, b) divides a, and d * gcd(a, b) divides b.  If d > 1, then this would contradict Lemma 5.13(3); thus d = 1 is the only common divisor of a / gcd(a, b) and b / gcd(a, b).

**Lemma 5.16** If the square of a positive integer n is even, then n is even.
**Proof.** Suppose n is odd.  Then we can write n = 2k + 1, and n^2 = (2k + 1)(2k + 1) = 4k^2 + 4k + 1 = 2(k^2 + 2k) + 1, which shows that n^2 is odd.  Taking the contrapositive, we conclude that if n^2 is even, then n is even.

**Lemma 5.17** Every Archimedean monoid with a smallest positive element is Euclidean.
**Proof.** Let e be the smallest positive element of the given Archimedean monoid.  We use a similar argument to the proof of Lemma 5.14.  If a > b, then a - b >= e, and if b > a, then b - a >= e; thus at every step, max(a, b) decreases by at least e.  Since the monoid is Archimedean, there exists some n in its QuotientType such that 0 <= max(a, b) - ne < e, i.e. max(a, b) - ne = 0.  Since max(a, b) is always positive, we conclude that the procedure can go through at most n iterations of the loop before terminating.

**Lemma 5.18** The rational numbers are a Euclidean monoid.
**Proof.** This is a restatement of the second part of Lemma 5.14.

**Lemma 5.19** In a Euclidean semiring, a * b = 0 implies a = 0 or b = 0.
**Proof.** Suppose a * b = 0 and b != 0.  Then we must have w(a * b) >= w(a).  But a * b = 0 and w(0) = 0; thus w(a) <= 0.  Since for any element x in a Euclidean semiring w(x) >= 0, we must have w(a) = 0.  Finally, w(a) = 0 implies a = 0.  Thus either b = 0 or a = 0, as desired.

**Lemma 5.20** gcd terminates on a Euclidean semiring.
**Proof.** At every iteration, w(max(a, b)) must decrease.  But max(a, b) is always positive; thus w(max(a, b)) is also positive.  If the procedure executes more than w(max(a0, b0)) iterations (where a0 and b0 are the initial values of the arguments), then w(max(a, b)) would become zero or negative, which is a contradiction.  We conclude that the procedure terminates after at most w(max(a0, b0)) iterations of the loop.

**Lemma 5.C** If remainder(a, b, rem) returns r, then there exists some q such that a = bq + r.
**Proof.** If a and b are both positive, then the claim follows immediately from the correctness of rem.  If a is positive and b is negative, then rem(a, -b) returns r' such that a = q(-b) + r'.  If r' = 0 then remainder returns 0, and a = (-q)b shows that the claim holds.  Otherwise, remainder returns b + r', and a = (-q - 1)b + (b + r') shows that the claim holds.  If a is negative and b is positive, then rem(-a, b) returns r' such that -a = qb + r'.  If r' = 0 then remainder returns 0, and a = (-q) b shows that the claim holds.  Otherwise, remainder returns b - r', and a = (-q - 1)b + (b - r') shows that the claim holds.  Finally, if a and b are both negative, then rem(-a, -b) returns r' such that -a = q(-b) + r', and remainder returns -r'; since a = qb + -r', the claim holds, and the proof is complete.

**Lemma 5.D** If remainder(a, b, rem) returns r, then |r| < |b|.
**Proof.** Since we assume that b is nonzero, if r = 0 there is nothing to prove; thus we only consider the case of nonzero r.  Suppose a and b are both positive; then by the correctness of rem, r = rem(a, b) < b, and |r| < |b| follows.  If a is positive and b is negative, then r = rem(a, -b) + b; since 0 < rem(a, -b) < -b, b < r < 0, so 0 < -r < -b, and |r| < |b|.  If a is negative and b is positive, then r = -rem(-a, b) + b; since 0 < rem(-a, b) < b, -b < -rem(-a, b) < 0, and 0 < r < b ,and |r| < |b| follows.  Finally, if a and b are both negative, then r = -rem(-a, -b); since 0 < rem(-a, -b) < -b, b < r < 0, and |r| < |b| follows.

**Lemma 5.E** If a is not divisible by b, then remainder(a, b, rem) will have the same sign as b.
**Proof.** If a and b are both positive, then remainder(a, b, rem) = rem(a, b), which returns a value 0 <= r < b; by our assumption that a is not divisible by b, r is positive.  (We will use this fact in subsequent cases as well.)

If a is negative and b is positive, then rem(-a, b) returns a positive value r' such that -a = qb + r', and 0 < r' < b.  Thus -b < -r' < 0, and 0 < b - r' < b, and remainder(a, b, rem) returns the positive value b - r'.

If a is positive and b is negative, then rem(a, -b) returns a positive value r' such that 0 < r' < -b.  Then b < b + r' < 0, and remainder(a, b, rem) returns the negative value b - r'.

Finally, if a is negative and b is negative, then rem(-a, -b) returns the positive value r' such that 0 < r' < -b.  Then 0 > -r' > b, and remainder(a, b, rem) returns the negative value -r'.

**Lemma 5.F** If a is divisible by b, then remainder(a, b, rem) always returns 0.
**Proof.** This follows immediately from the definition of remainder together with the assumed correctness of rem.

**Lemma 5.G** a is congruent to remainder(a, b, rem) mod b.
**Proof.** If a is divisible by b, then the claim follows from Lemma 5.F, so we only need to consider the case where remainder(a, b, rem) is nonzero.  If a and b are both positive, then the claim follows from the correctness of rem.  If a is positive and b is negative, then remainder(a, b, rem) = b + r', where a = q(-b) + r'.  Thus a is congruent to r' mod b, so a is congruent to b + r' mod b.  If a is negative and b is positive, then remainder(a, b, rem) = b - r', where -a = qb + r'.  Thus a = (-q)b - r', and a is congruent to -r' mod b, so a is also congruent to b - r' mod b.  Finally, if a and b are both negative, then remainder(a, b, rem) = -r', where -a = q(-b) + r'.  Thus a = qb - r', which shows that a is congruent to r' mod b.

**Lemma 5.21A** remainder is correct whenever rem is correct.
**Proof.** Lemma 5.D shows that the second property, |remainder(a, b)| < |b|, holds.  If b < 0, then Lemmas 5.D, 5.E, and 5.G show that remainder(a, b) is the unique element in the range (b, 0] congruent to a mod b; since a + b and a - b are both also congruent to a, transitivity of congruence shows that remainder(a + b, b, rem) = remainder(a - b, b, rem) = remainder(a, b, rem).  Similarly, if b > 0, then Lemmas 5.D, 5.E, and 5.G show that remainer(a, b) is the unique element in the range [0, b) congruent to a mod b; since a + b and a - b are also congruent to a, again we have remainder(a + b, b, rem) = remainder(a - b, b, rem) = remainder(a, b, rem); thus the third property holds.  The first property depends also on quotient; we will prove its correctness when we prove that quotient_remainer is correct.

**Lemma 5.H** If qr(a, b, op) returns (q, r), then a = qb + r.
**Proof.** We begin with the case where b divides a.  If a and b are both positive, then the claim follows from the assumed correctness of op.  If a is positive and b is negative, then op(a, -b) returns the pair (q', 0), where a = q'(-b), qr returns the pair (-q', 0), and a = (-q')b + 0 holds.  If a is negative and b is positive, then op(-a, b) returns the pair (q', 0), where -a = q'b, qr returns the pair (-q', 0), and a = (-q')b + 0 holds.  If a and b are both negative, then op(-a, -b) returns the pair (q', 0) where -a = -q'b, qr returns the pair (q', 0), and a = q'b holds.

Next, we consider the case where b does not divide a.  If a and b are both positive, then the claim follows from the assumed correctness of op.  If a is positive and b is negative, then op(a, -b) returns the pair (q', r') where a = q'(-b) + r', qr returns the pair (-q' - 1, b + r'), and a = (-q' - 1)b + (b + r') holds.  If a is negative and b is positive, then op(-a, b) returns the pair (q', r') where -a = q'b + r', qr returns the pair (-q' - 1, b - r'), and a = (-q' - 1)b + b - r' holds.  Finally, if a and b are both negative, then op(-a, -b) returns the pair (q', r') where -a = q'(-b) + r', qr returns the pair (q', -r'), and a = q'b + -r' holds.

**Lemma 5.21B** quotient_remainder is correct whenever op is correct.
**Proof.** Lemma 5.H shows that the first property (a = qb + r) holds.  Since the remainder part of quotient_remainder is implemented identically to the 'remainder' procedure, Lemma 5.21A implies that the second and third properties (|r| < |b| and congruence) also hold.

**Lemma 6.1**

    0 <= j <= i ^ weak_range(f, i) implies weak_range(f, j)

**Proof.** Take any k in DistanceType(I) such that 0 <= k <= j.  Then 0 <= k <= i, so weak_range(f, i) implies that successor^k(f) is defined.

**Lemma 6.2** (f + n) + m = f + (n + m)
**Proof.** If n = 0, then f + n = f and n + m = m; thus (f + n) + m = f + m and f + (n + m) = f + m.  Consider n > 0, and suppose the claim is true for predecessor(n).  Then

    f + (n + m) = f + successor(predecessor(n) + m)
                = successor(f + (predecessor(n) + m))
                = successor((f + predecessor(n)) + m)
                = (f + predecessor(n)) + successor(m)
                = (f + predecessor(n)) + successor(m + 0)
                = (f + predecessor(n)) + m + successor(0)
                = ((f + predecessor(n)) + successor(0)) + m
                = (f + (predecessor(n) + successor(0))) + m
                = (f + successor(predecessor(n) + 0)) + m
                = (f + successor(predecessor(n))) + m
                = (f + n) + m

**Lemma 6.3** successor is defined for every iterator in a half-open range and for every iterator except the last in a closed range.
**Proof.** Suppose (f, n) is a weak or counted range.  Then successor^k(f) is defined for each 0 <= k <= n, which implies that successor(successor^k(f)) is defined for each 0 <= k < n.  Since {successor^k(f), 0 <= k < n} comprise every iterator in a half-open range, or every iterator except the last in a closed range, the claim follows for weak and counted ranges.  If [f, l) is a half-open bounded range, then [[f, l - f)) is a half-open counted range; we have already proved that successor is defined for every iterator in [[f, l - f|), and since [[f, l - f|) and [f, l) are the same range, it follows that successor is defined for every iterator in [f, l).  Similarly, if [f, l] is a closed bounded range, then [[f, l - f]] is a closed counted range; we have already proved that successor is defined for every iterator except the last in [[f, l - f]], and since [[f, l - f]] and [f, l] are the same range, it follows that successor is defined for every iterator except the last in [f, l].

**Lemma 6.4** If i is in [f, l), both [f, i) and [i, l) are bounded ranges.
**Proof.** Since [f, l) is equivalent to the half-open counted range [[f, l - f|), i is in [f, l) implies i = successor^k(f) for some 0 <= k < l - f.  Note that by definition of distance, i = successor^k(f) and i - f = k.  Since counted ranges are weak ranges, Lemma 6.1 implies that [[f, k|) = [[f, i - f|) is a counted range, i.e. [f, i) is a bounded range.  Next, note that successor^j(i) is defined and distinct for each 0 <= j <= (l - f) - k; thus [[i, (l - f) - k|) is a counted range.  Finally, since l = successor^{l-f}(f) = successor^{(l-f)-k}(successor^k(f)) = successor^{(l-f)-k}(i), it follows that [[i, (l - f) - k|) is precisely the bounded range [i, l).

**Lemma 6.5.** i is not an element of [[i, 0|) and i is not an element of [i, i).
**Proof.** [[i, 0|) is defined as the sequence of iterators {successor^k(i) | 0 <= k < 0}; since there are no k for which 0 <= k < 0, [[i, 0|) is the empty sequence of iterators.  Since [i, i) is defined as [[i, i - i|) and i - i is defined as 0 for any iterator i, [i, i) is also the empty sequence of iterators.  We conclude that i is neither an element of [[i, 0|) nor an element of [i, 0), since i is not an element of the empty set.

**Lemma 6.6** Empty ranges have neither first nor last elements.
**Proof.** The proof of Lemma 6.5 shows that an empty range [[i, 0|) or [i, i) actually does correspond to an empty sequence of iterators, and an empty sequence has neither a first nor a last element.

**Lemma 6.7**
    (1) The size of a half-open weak range [[f, n|) is n
    (2) The size of a closed weak range [[f, n]] is n + 1
    (3) The size of a half-open bounded range [f, l) is l - f
    (4) The size of a closed bounded range [f, l] is (l - f) + 1
**Proof.**
    (1) [[f, n|) is the sequence of iterators {successor^k(f) | 0 <= k < n}; since there are n values of k such that 0 <= k < n, the sequence has n terms.  Note that for a weak range that's not a counted range, even though the sequence of iterators has n terms, the set of iterators that appear in the sequence might have fewer than n elements.
    (2) [[f, n]] is the sequence of iterators {successor^k(f) | 0 <= k <= n}; since there are n + 1 values of k such that 0 <= k <= n, the sequence has n + 1 terms.
    (3) This follows from the fact that [f, l) is the same sequence as [[f, l - f)).
    (4) This follows from the fact that [f, l] is the same sequence as [[f, l - f]].

**Lemma 6.8** If p is a predicate and [f, l) is a p-partitioned range:

    (1) (forall m in [f, l)) !p(source(m)) implies (forall j in [f, m]) !p(source(j))
    (2) (forall m in [f, l)) p(source(m)) implies (forall j in [m, l) p(source(j))

**Proof.**

(1) We will prove the contrapositive.  Suppose p(source(j)) for some j in [f, m].  Then by definition of a p-partitioned range, p(source(k)) for each k in [j, l).  In particular, p(source(m)).

(2) This follows directly from the definition of a p-partitioned range.

**Lemma 6.A** If i precedes j in an r-increasing range of iterators, then !r(j, i).
**Proof.** We proceed by induction on j - i.  The case j - i = 1 follows immediately from the definition of an increasing range.  Suppose the claim is true for n - 1, and suppose j - i = n, i.e. j - successor(i) = n - 1.  By definition of an increasing range together with our inductive hypothesis, the following are the only possible cases:

(1) If r(i, successor(i)) and r(successor(i), j), then r(i, j) by transitivity and !r(j, i) by weak-trichotomy.
(2) If e(i, successor(i)) and r(successor(i), j), then r(j, i) would imply (by transitivity) that r(successor(i), i), which contradicts weak-trichotomy (e(i, successor(i)) implies e(successor(i), i) since equivalence relations are symmetric).
(3) If r(i, successor(i)) and e(successor(i), j), then r(j, i) would imply (by transitivity) that r(j, successor(i)), which contradicts weak-trichotomy (e(successor(i), j) implies e(j, successor(i)) since equivalence relations are symmetric).
(4) If e(i, successor(i)) and e(successor(i), j), then e(i, j) by transitivity and !r(j, i) by weak-trichotomy.

In each case, !r(j, i), and the induction is complete.

**Lemma 6.10** In an increasing half-open bounded range (f, l), for any value a of the value type of the range, the range is partitioned by the following two predicates:

    lower_bound_a(x) <=> !r(x, a)
    upper_bound_a(x) <=> r(a, x)

**Proof.** Suppose !r(x, a) holds for the value x of some iterator i in the range.  Let j be another iterator in the range, where i precedes j, and let y be the corresponding value.  By Lemma 6.A, !r(y, x), so by weak-trichotomy, either r(x, y) or e(x, y).  In the case r(x, y), if r(y, a) holds, then transitivity would imply r(x, a), which contradicts !r(x, a).  In the case e(x, y), note that by weak-trichotomy, !r(x, a) implies either r(a, x) or e(a, x).  If r(a, x), then r(y, a) would imply r(y, x) by transitivitity, which, together with e(x, y), contradicts weak-trichotomy.  If e(a, x), then transitivity of e implies e(a, y), so r(y, a) would again contradict weak-trichotomy.  Thus !r(y, a); in particular, if !r(source(i), a) holds for any iterator i in the range, then !r(source(j), a) must also hold for any iterator j in the range such that i precedes j, and we conclude that the predicate lower_bound_a partitions the range of iterators.

Next, suppose r(a, x) holds for the value x of some iterator i in the range.  Let j be another iterator in the range, where i precedes j, and let y be the corresponding value.  By Lemma 6.A, !r(y, x), so by weak-trichotomy either r(x, y) or e(x, y).  If r(x, y), then transitivity of r implies r(a, y).  If e(x, y), then e(a, y) would imply e(a, x) by transitivity of e, which would contradict trichotomy (we cannot have both r(a, x) and e(a, x)), and r(y, a) would imply r(y, x) by transitivity of r, which would again contradict trichotomy (we cannot have both r(y, x) and e(x, y)).  We conclude that r(a, y) holds; in particular, if r(a, source(i)) holds for any iterator i in the range, then r(a, source(j)) must also hold for any iterator j in the range such that i precedes j, and we conclude that the predicate upper_bound_a partitions the range of iterators.

**Lemma 6.11** The lower bound iterator for a given value a precedes or equals the upper bound iterator.
**Proof.** Let l be the lower bound iterator for a; then l is the first iterator for which !r(source(l), a) holds.  Next, let u be the upper bound iterator for a; then r(a, source(u)) holds, and by weak-trichotomy, !r(source(u), a).  Since l was defined as the first iterator for which !r(source(l), a) holds, and u is an iterator for which !r(source(u), a) holds, we conclude that l must precede or equal u.
