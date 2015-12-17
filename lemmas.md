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

**Proof.** Suppose !r(x, a) holds for the value x of some iterator i in the range.  Let j be another iterator in the range, where i precedes j, and let y be the corresponding value.  By Lemma 6.A, !r(y, x), so by weak-trichotomy, either r(x, y) or e(x, y).  In the case r(x, y), if r(y, a) holds, then transitivity would imply r(x, a), which contradicts !r(x, a).  In the case e(x, y), note that by weak-trichotomy, !r(x, a) implies either r(a, x) or e(a, x).  If r(a, x), then r(y, a) would imply r(y, x) by transitivity, which, together with e(x, y), contradicts weak-trichotomy.  If e(a, x), then transitivity of e implies e(a, y), so r(y, a) would again contradict weak-trichotomy.  Thus !r(y, a); in particular, if !r(source(i), a) holds for any iterator i in the range, then !r(source(j), a) must also hold for any iterator j in the range such that i precedes j, and we conclude that the predicate lower_bound_a partitions the range of iterators.

Next, suppose r(a, x) holds for the value x of some iterator i in the range.  Let j be another iterator in the range, where i precedes j, and let y be the corresponding value.  By Lemma 6.A, !r(y, x), so by weak-trichotomy either r(x, y) or e(x, y).  If r(x, y), then transitivity of r implies r(a, y).  If e(x, y), then e(a, y) would imply e(a, x) by transitivity of e, which would contradict trichotomy (we cannot have both r(a, x) and e(a, x)), and r(y, a) would imply r(y, x) by transitivity of r, which would again contradict trichotomy (we cannot have both r(y, x) and e(x, y)).  We conclude that r(a, y) holds; in particular, if r(a, source(i)) holds for any iterator i in the range, then r(a, source(j)) must also hold for any iterator j in the range such that i precedes j, and we conclude that the predicate upper_bound_a partitions the range of iterators.

**Lemma 6.11** The lower bound iterator for a given value a precedes or equals the upper bound iterator.
**Proof.** Let l be the lower bound iterator for a; then l is the first iterator for which !r(source(l), a) holds.  Next, let u be the upper bound iterator for a; then r(a, source(u)) holds, and by weak-trichotomy, !r(source(u), a).  Since l was defined as the first iterator for which !r(source(l), a) holds, and u is an iterator for which !r(source(u), a) holds, we conclude that l must precede or equal u.

**Lemma 6.12** For a forward iterator, the total number of successor operations performed by partition_point_n is less than or equal to the size of the range.
**Proof.** We will show that partition_point_n performs at most n successor operations.  If n = 0, then the procedure returns immediately without performing any successor operations, so the claim trivially holds.  Suppose n > 0, and the claim is true for all values less than n.  In this case, the procedure performs h = floor(n / 2) successor operations to calculate m = f + h, and then branches to one of two possible cases:

(1) If p(source(m)) returns true, then the procedure sets n to h, which reduces the problem to a subproblem of size h.  By our inductive hypothesis, the procedure performs at most h successor operations for the subproblem, for a total of 2h (which is at most n) successor operations.

(2) If p(source(m)) returns false, then the procedure performs one more successor operation and then sets n to n - successor(h), which reduces the problem to a subproblem of size n - successor(h).  By our inductive hypothesis, the procedure performs at most n - successor(h) successor operations for the subproblem, for a total of at most h + 1 + n - successor(h) = n successor operations.

**Lemma 6.14** If successor is defined on bidirectional iterators i and j, then successor(i) = successor(j) implies i = j.
**Proof.** By definition of a bidirectional iterator, if successor(i) is defined, then predecessor(successor(i)) = i.  Similarly, if successor(j) is defined, then predecessor(successor(j)) = j.  Thus by regularity of predecessor and the fact that successor(i) = successor(j) it follows that predecessor(successor(i)) = predecessor(successor(j)), i.e. i = j.

**Lemma 7.1**

    height_recursive(x) <= weight_recursive(x)

**Proof.** We will proceed by induction on the number of descendants of x (which is assumed to be finite, by the precondition that x is a tree).  If x has no proper descendants, then both the height and the weight return 0, and there is nothing to prove.  Otherwise, let hl, wl be the height and weight of the left successor, and let hr, wr be the height and weight of the right successor.  By the inductive hypothesis, hl <= wl and hr <= wr.  Since hl, wl, hr, and wr are all positive, we have wl + wr >= hl + hr >= max(hl, hr); thus successor(wl + wr) >= successor(max(hl, hr)), and since these are precisely the values returned by the weight and height procedures, respectively, the proof is complete.

**Lemma 7.2** If x and y are bidirectional bifurcate coordinates,

    left_successor(x) = left_successor(y) implies x = y
    left_successor(x) = right_successor(y) implies x = y
    right_successor(x) = right_successor(y) implies x = y

**Proof.**

     By definition of a bidirectional bifurcate coordinate, whenever right_successor(i) is defined, we have predecessor(right_successor(i)) = i; similarly, whenever left_successor(i) is defined, we have predecessor(left_successor(i)) = i.  Thus the implications above follow immediately from regularity of predecessor.

**Lemma 7.A** If v != post and !empty(x) before executing traverse_step(v, x), and if v = v' and x = x' after executing, then x' is a descendant of x.
**Proof.** In the cases where v != post, traverse_step either sets x to its left successor, sets x to its right successor, or doesn't change x.  In each case, x' is a descendant of x.

**Lemma 7.B** If the descendants of x form a tree, x = x0, and v = pre initially, then we will have x = x0, v = post after finitely many calls to traverse_step(v, x).
**Proof.** We will proceed by induction on the height h of the tree rooted at x.  If h = 1, then x has neither a left nor a right successor, so one call will set v = in without changing x, and a second call will set v = post without changing x.  If h > 1, suppose the claim holds for a tree of height h - 1.

If x0 has a left successor, then one call will set x to the left successor xl of x0 without changing v.  By our inductive hypothesis (the tree rooted at xl has height h - 1 because the maximum sequence of successors from xl can be extended to a sequence of successors from x0 with one additional successor), after finitely many more calls, we will have x = xl and v = post.  Since x0 is the predecessor of xl, an additional call will set v = in and x = x0.  Otherwise, if x0 does not have a left successor, then one call will set v = in without changing x.  Either way, x = x0 and v = in after finitely many calls.

Now x = x0 and v = in; if x0 has a right successor, then one call will set x to the right successor xr of x0 and set v = pre.  By our inductive hypothesis, (the tree rooted at height xr has a height h - 1), after finitely many more calls, we will have x = xr and v = post.  Since x0 is the predecessor of xr, an additional call will set x = x0 without changing v.  Otherwise, if x0 does not have a right successor, then one call will set v = post without changing x.  Either way, x = x0 and v = post after finitely many calls, and the proof is complete.

**Lemma 7.C** If the descendants of x0 form a tree, y is a descendant of x0, v = pre, and x = x0 initially, then we will have y == x after finitely many calls to traverse_step(v, x).
**Proof.** We will proceed by induction on the height h of the tree rooted at x0.  If h = 1, then x0 is the only element of the tree, so y is a descendant of x0 implies y == x without any calls.  Suppose h > 1, and the claim holds for a tree of height h - 1.

If x0 == y then there is nothing to prove, so we can assume x0 != y.

If x0 has a left successor and y is a descendant of its left successor, one call will set x to the left successor xl of x0, and by our inductive hypothesis, finitely many more calls will set x to y.

If x0 does not have a left successor, then a single call will set v = post, x = x0.  If x0 does have a left successor xl but y is not a descendant of xl, then by Lemma 7.B, after finitely many more calls we will have v = post, x = xl, and by definition of the procedure, one more call will set v = in, x = x0.  Either way, v = in and x = x0 after finitely many calls.  Since y is a descendant of x0 and y is neither x0 nor a descendant of xl, we know that x0 has a right successor xr and that y is a descendant of xr, and by our inductive hypothesis, finitely many more calls will set x to y.

**Lemma 7.E** If x = x0 and v = pre initially, then upon repeated calls to traverse_step(v, x), until we have x == x0 && v == post, every intermediate value of x will be a descendant of x0.

**Proof.** If x0 has no left or right successor, then one call will set v = in without changing x, and the second call will set v = post without changing x, and the claim holds.  If x0 has a left successor xl, then one call will set x = xl without changing v; by our inductive hypothesis, subsequent intermediate values of x will be descendants of xl (thus descendants of x0) until x = xl && v == post, and one more call will set x = x0, v = in.  If x0 has no left successor, then one call will set x = x0, v = in.  Next, if x0 has a right successor xr, then one call will set x = xr and v = pre; by our inductive hypothesis, subsequent intermediate values of x will be descendants of xr (thus descendants of x0) until x = xr && v == post, and one more call will set x = x0, v = post.  If x0 has no right successor, then one call will set x = x0, v = post.

**Lemma 7.F** If x = x0 and v = pre initially, then upon repeated calls to traverse_step(v, x), the x will take on the value of every descendant of x0 before x == x0 && v == post holds.
**Proof.** If x0 has no left or right successors then there is nothing to prove.  If x0 has a left successor xl then Lemma 7.E and our inductive hypothesis imply that x will take on the value of every descendant of xl (and only those values) before x == xl && v == post holds, and one more call will set x = x0, v = in.  If x0 has no left successor then a single call will set x = x0, v = in.  Next, if x0 has a right successor xr then Lemma 7.E and our inductive hypothesis imply that x will take on the value of every descendant of xr (and only those values) before x == xr && v == post holds, and one more call will set x = x0, v = post.  If x0 has no right successor then a single call will set x = x0, v = post.  Since the descendants of x0 are precisely x0, the descendants of its left successor (if it exists), and the descendants of its right successor (if it exists), the proof is complete.

**Lemma 7.G** If the descendants of x0 form a tree and y is a descendant of x0, then reachable(x0, y) will return true.
**Proof** By Lemma 7.C, and the definition of reachable (which ensures that v = pre initially), finitely many calls to traverse_step(v, x) will set x == y.  By Lemma 7.F, this will occur before x == root && v == post holds.

**Lemma 7.H** If the descendants of x0 form a tree and y is a descendant of x0, and if x = x0, v = pre initially, then repeated calls to traverse_step(v, x) will set x = y, v = pre before x == y, v == in or x == y, v == post hold.
**Proof.** Lemma 7.F ensures that repeated calls will indeed set x == y.  We will proceed by induction on the height of the tree rooted at x0.  If y == x0 then x == y, v = pre initially, so there is nothing to prove.

Suppose x0 has a left successor xl.  If y is a descendant of xl, then the claim follows by our inductive hypothesis.  Otherwise, by Lemma 7.E, we will have x == xl, v = post before x == y holds, and one more call will set x = x0, v = in.  If x0 has no left successor, then a single call will set x = x0, v = in.

We have already considered the cases where y == x0 or y is a descendant of the left successor of x, thus we can assume neither of these cases hold.  By definition of a descendant, y must be a descendant of the right successor xr of x (which must exist).  In every possible case, repeated calls set x = x0, v = in without ever setting x = y.  One more call will set x = xr and v = in, and the claim follows by our inductive hypothesis.

**Lemma 7.3** If reachable returns true, v = pre right before the return.
**Proof.** Suppose reachable returns true.  Then by Lemma 7.E, and the definition of reachable (in particular, the fact that v == pre holds before any traversal calls), y must be a descendant of x.  Furthermore, by Lemma 7.H, reachable will set x = y, v = pre before either of x == y, v == in or x == y, v == post holds.

**Lemma 7.4** For bidirectional bifurcate coordinates, trees are isomorphic when simultaneous traversals take the same sequence of visits.
**Proof.** We will show by induction that if simultaneous traversals on two trees of height h take the same sequence of visits, then there exists an isomorphism f between the two trees.  Two trees of height 1 (consisting of just a root) are always isomorphic, so the base case is trivial.

Suppose h > 1, the claim is true for h - 1, and simultaneous traversals on two trees of height h take the same sequence of visits.  Let v0 and v1 (whose initial values are both pre) be the visits maintained by the two simultaneous traversals, let x0 and x1 be the coordinates maintained by the two simultaneous traversals, and consider the following cases:

(1) If after one traversal step, v0 = v1 = pre, then both trees' roots had a left successor.  By Lemmas 7.E and 7.F, the two simultaneous traversals will traverse precisely the elements of the two left subtrees before setting v0 = v1 = in and x0 and x1 back to their initial values.  Thus by our inductive hypothesis, there exists an isomorphism fl between the two left subtrees.

(2) If after one traversal step, v0 = v1 = in, then both trees' roots had no left successor.

In either case, we now have v0 = v1 = in and x0, x1 equal to their original values.  We next consider the following cases:

(1) If after one more traversal step, v0 = v1 = pre, then both trees' roots had a right successor.  By Lemmas 7.E and 7.F, the two simultaneous traversals will traverse precisely the elements of the two right subtrees before setting v0 = v1 = post and x0 and x1 back to their initial values.  Thus by our inductive hypothesis, there exists an isomorphism fr between the two right subtrees.

(2) If after one more traversal step, v0 = v1 = post, then both trees' roots had no right successor.

In either case, we now have v0 = v1 = post and x0, x1 equal to their original values.

Since the x0 and x1 are the roots of two trees, for each tree, the left and right subtrees are disjoint, and the root does not appear in either subtree.  Thus we can define a function f that maps x0 to x1, and maps the values of the left and right subtrees (if one or both exists) via fl and fr, respectively.  Whenever x0 and f(x0) have a left successor, f maps the left successor of x0 to the left successor of f(x0), since fl is an isomorphism between the two left subtrees that maps the root of the first (i.e. the left successor of x0) to the root of the second (i.e. the left successor of f(x0)).  Similarly, whenever x0 and f(x0) have a right successor, f maps the right successor of x0 to the right successor of f(x0).  For any proper descendants of x, the fact that f preserves left and right descendants follows from the fact that fl and fr are isomorphisms.  Thus we conclude that f is an isomorphism between the two trees.

**Lemma 8.1** For each of the ranges [h, t] returned by split_linked, h = l <=> t = l.
**Proof.** First note that h0 = t0 = l and h1 = t1 = l are true initially.

Next, note that every assignment of h and/or t sets h and/or t to the current value of f, and that such assignments are guarded by a check that bypasses the assignment(s) if f == l holds.  Thus if at any point h != l or t != l, then this must hold for the rest of the procedure.

Furthermore, every assignment of h is immediately followed by an assignment to t, and the previous paragraph shows that (a) assignments never set h or t to l, and (b) once h and/or t has been set to a value that’s not equal to l, h and/or t will have a value different from l for the rest of the procedure.  Thus we can conclude that if h != l, then t != l.

Finally, we need to show that if h == l, then t == l.  We will consider only h0 and t0 (the case of h1 and t1 is analogous).  If f == l initially, then the procedure returns immediately with h == l and t == l.  If f != l and !p(f) initially, then the procedure immediately sets both h0 and t0 to a value not equal to l, and h0 != l holds for the rest of the procedure.  If f != l and p(f) initially, then the procedure jumps to s1 without changing h0 and t0 from their default values.

Now the procedure is at the beginning of the s1 label with h0 == l and t0 == l.  Write l = successor^k(f).  We will show, by induction on k, that if the procedure returns with h0 == l, then we will also have t0 == l.  If k == 0, then f == l, and the procedure returns immediately.  Suppose k > 0, and the inductive hypothesis holds for k - 1.  If !p(f), then the procedure sets h0 to f (which is not equal to l), and since any subsequent assignment to h0 cannot set h0 back to l, the procedure returns with h0 != l, so there is nothing more to prove for this case.  If p(f), then the procedure sets f = successor(f) inside the advance_tail(t1, f) call and then jumps to the beginning of s1, at which point we still have h0 == l, t0 == l, but now l = successor^{k-1}(f).  By the inductive hypothesis, if the procedure returns with h == 0, then it also returns with t == 0.

By combining the results of the two previous paragraphs, we can conclude that if h0 == l when the procedure returns, then also t0 == l (and by an analogous argument with s0 in place of s1, we can show that this is also the case for h1 == l), which completes the proof.

**Lemma 8.2** split_linked is a precedence-preserving link rearrangement.
**Proof.** We will first show that in the entire body of the procedure, either t0 == l or t0 precedes f in the original input range (the claim that either t1 == l or t1 precedes f is handled analogously).  Initially, t0 == l.  f is only changed through calls to advance_tail and link_to_tail.  Calling advance_tail(t1, f) or link_to_tail(t1, f) will change neither the fact that t0 == l or the fact that t0 precedes f in the original input range (since if t_0 precedes f, then also t0 precedes successor(f)).  Calling advance_tail(t0, f) or link_to_tail(t0, f) will set t0 = f, f = successor(f), and since f precedes successor(f) in the original input range, the stated condition still holds.

Next, note that in the entire body of the procedure, f precedes successor(f) in the original input range: if link_to_tail has not been called with t0 or t1 equal to the current value of f then there is nothing to prove, and if it has, the previous paragraph shows that f still precedes its successor in the original input range (since when link_to_tail was called, the first argument precedes the second argument in the original input range).

Finally, we will show that in the entire body of the procedure, either h0 == l, or for every adjacent pair of iterators i, j in the closed bounded range [h0, t0], i precedes j in the original input range (the claim for h1, t1 is handled analogously).

Initially, the claim holds because the first disjunct h0 == l holds.

Setting h1 = f, calling advance_tail(t1, f), or calling link_to_tail(t1, f) changes neither h0 or t0, so if the claim held before executing any of these statements, the claim will still hold after executing any of these statements.

Setting h0 = f is immediately followed by a call to advance_tail(t0, f), and the result of these two calls will be h0 == f, t0 == f.  Subsequently, there are no adjacent iterators in the singleton range [h0, t0] and nothing to prove.

Calling advance_tail(t0, f) either follows an assignment h0 = f, and thus sets t0 == h0 (before entering any of the states, or in state s1), in which case there are no adjacent iterators in the singleton range [h0, t0], or occurs in a state where successor(t0) = f holds.  We proved above that t0 always precedes f in the original input range; thus if the condition was true before the call to advance_tail, then condition will still be true after the call to advance_tail.

Finally, calling link-to_tail(t0, f) will set successor(t0) to f and then set t0 = f.  Again, since t0 always precedes f in the original input range, if the condition was true before the call to advance_tail, then the condition will still be true after the call to advance_tail.

Given the condition “either h0 == l or for every adjacent pair of iterators i, j in the closed bounded range [h0, t0], i precedes j in the original input range”, we have shown that (a) the condition holds initially, and (b) every statement in the body of the procedure preserves the condition.  Thus the condition holds when the procedure returns.  Since the condition for h1, t1 is handled analogously, we conclude that split_link is a precedence-preserving link rearrangement.

**Lemma 8.3** If a call combine_linked_nonempty(f0, l0, f1, l1, r, s) returns (h, t, l), h equals f0 or f1, and, independently, l equals l0 0r l1.
**Proof.** combine_linked_nonempty only assigns h once at the beginning of the procedure, and it can only assign h to either the f0 or f1.  Furthermore, combine_linked_nonempty never assigns l0 or l1.  Finally, the only possible return values are (h, t, l0) and (h, t, l1), so the lemma holds.

**Lemma 8.4** When state s2 is reached, t is from the original half-open range (f0, l0), successor(t) = l0, and f1 != l1.
**Proof.** There is only one ‘goto s2’ statement, and in  this case, we have successor(t) == f0 and f0 == l0; thus successor(t) == l0 holds.  If we reached s0 from the first ‘goto s0’ statement, then f1 != l1 by the procedure’s precondition.  Otherwise, we reached s0 from the second ‘goto s0’ statement, in which case the goto statement only executes when f1 == l1 does    not hold.  The corresponding claim for s3 is proved analogously.  

**Lemma 8.5** combine_linked_nonempty is a precedence-preserving link rearrangement.
**Proof.** We will begin by showing that it is a link rearrangement. The input ranges are pairwise disjoint by the precondition; there is only one output range, so we do not need to show that the output ranges are pairwise disjoint.  We will demonstrate conservation by the following sequence of lemmas.

  **Lemma 8.5.1** At any point in the procedure, f0 = successor^j(f0’) for some j, where f0’ is the original value of the argument f0.  Furthermore, if l0 = successor^k(f0’), then j <= k.  Similarly, at any point in the procedure, f1 = successor^j(f1’) for some j, where f1’ is the original value of the argument f1.  Furthermore, if l1 = successor^k(f1’), then j <= k.
  **Proof.** We will show that the condition holds initially, and that every statement preserves this condition.
  Initially, f0 = f0’, so the condition trivially holds.  The only statements that modify f0 are calls to advance_tail or link_tail with f0 as the second argument.  In this case, the call sets f0 = successor(f0); thus if f0 = successor^j{f0’} before the call, then f0 = successor^{j+1}(f0’) after the call.  Furthermore, note that advance_tail or link_tail is only called then f0 == l0 does not hold; thus j < k before the call, so j <= k after the call, and the entire condition still holds after the call.  The claim for f1 is handled analogously.
  **Lemma 8.5.2** In state s0, successor(t) = f0, and in state s1, successor(t) = f1.
  **Proof.** Both ‘goto s0’ statements follow a call to advance_tail(t, f0), which sets t = f0, f0 = successor(f0); thus the claim follows by regularity of successor.  The claim for s1 is handled analogously.
  **Lemma 8.5.3** At any point in the procedure, if h and t have been initialized, then every iterator in [h, t] appears in either [f0, l0) or [f1, l1).
  **Proof.** We will show that the condition holds initially, and that every block of statements (i.e. sequence of statements enclosed within curly braces) preserves the condition.
  Initially, h and t have not been initialized, so the condition trivially holds.  Note that h and t are initialized one of the first two blocks of the procedure, so for all subsequent blocks we can assume that h and t have been initialized.
   The block { h = f1; advance_tail(t, f1); goto s1; } sets [h, t] to the range with the single element f1, and the precondition f1 != l1 implies that this element appears in [f1’, l1).
  Similarly, the block { h = f0; advance_tail(t, f0); goto s0; } sets [h, t] to the range with the single element f0, and the precondition f0 != l0 implies that this element appears in [f0’, l0).
  The block { link_to_tail(t, f1); goto s1; } sets successor(t) to s1 and then sets t to f1; in particular, this extends the range [h, t] by the single element f1, and Lemma 8.5.1 implies that this element appears in [f1’, ll).
  Similarly, the block { link_to_tail(t, f0); goto s0; } sets successor(t) to s0 and then sets t to f0; in particular, this extends the range [h, t] by the single element f0, and Lemma 8.5.1 implies that this new element appears in [f0’, l0).
  The block { advance_tail(t, f0); goto s0; } occurs in state s0, and Lemma 8.5.2 implies that successor(t) = f0 in this case; thus this block again extends the range [h, t] by the single element f0, and Lemma 8.5.1 again implies that this new element appears in [f0’, l0).
  Finally, the block { advance_tail(t, f1); goto s1; } occurs in state s1, and Lemma 8.5.2 implies that successor(t) = f1 in this case; thus this block again extends the range [h, t] by the single element f1, and Lemma 8.5.1 again implies that this new element appears in [f1’, l1).
  **Lemma 8.5.4** If the procedure returns (h, t, l), then every iterator in [h, l) appears in either [f0, l0) or [f1, l1).
  **Proof.** By Lemma 8.5.3, at the beginning of the s2 label, every iterator in [h, t] appears in either [f0, l0) or [f1, l1).    By Lemma 8.5.1, at the beginning of the s2 label, f1 = successor^j(f1’), where f1’ is the original value of the argument f1 and j <= k (where successor^k(f1’) = l1).  Thus after the call to set_link(t, f1), the range [h, l) contains the elements of [h, t] together with the elements successor^j(f1’), successor^{j+1}(f1’), …, successor^k(f1’), all of which appear in either [f0, l0) or [f1, l1).
  Similarly, by Lemma 8.5.3, at the beginning of the s3 label, every iterator in [h, t] appears in either [f0, l0) or [f1, l1).    By Lemma 8.5.1, at the beginning of the s3 label, f0 = successor^j(f0’), where f0’ is the original value of the argument f0 and j <= k (where successor^k(f0’) = l0).  Thus after the call to set_link(t, f0), the range [h, l) contains the elements of [h, t] together with the elements successor^j(f0’), successor^{j+1}(f0’), …, successor^k(f0’), all of which appear in either [f0, l0) or [f1, l1).
  **Lemma 8.5.5** At any point in the procedure, every element in [f0’, l0), [f1’, l1) appears in either [h, t], [f0, l0), or [f1, l1).
  **Proof.** Initially, f0 = f0’ and f1 = f1’, so the claim follows trivially.  Every subsequent statement that removes an element from [f0, l0) adds that same element to [h, t]; similarly, every subsequent statement that removes an element from [f1, l1) adds that same element to [h, t].
  **Lemma 8.5.6** If the procedure returns (h, t, l), then every iterator in [f0, l0) and [f1, l1) appears in [h, l).
  **Proof.** At s2, we have f0 == l0, so [f0, l0) is empty, and by Lemma 8.5.5, every iterator in [f0’, l0), [f1’, l1) appears in either [h, t] or [f1, l1).  Setting successor(t) to f1 and l to l1 results in a range [h, l) that contains every iterator in both [h, t] and [f1, l1), i.e. every iterator in [f0’, l0) and [f1’, l1).
  Similarly, at s3, we have f1 == l1, so [f1, l1) is empty, and by Lemma 8.5.5, every iterator in [f0’, l0), [f1’, l1) appears in either [h, t] or [f0, l0).  Setting successor(t) to f0 and l to l0 results in a range [h, l) that contains every iterator in both [h, t] and [f0, l0), i.e. every iterator in [f0’, l0) and [f1’, l1).

Lemma 8.5.4 and Lemma 8.5.6 together demonstrate conservation.  Finally, we will show that the procedure is precedence-preserving.  By Lemma 8.5.1, at any point in the procedure, the iterators in [f0, l0) and [f1, l1) that appear in the original ranges [f0’, l0) and [f1’, l1) have the same precedence relations that they do in the original ranges.
  **Lemma 8.5.7** At s2, t precedes f1, and at s3, t precedes f0.
  **Proof.** This follows immediately from Lemma 8.5.2 and the fact that whenever successor is defined, an iterator precedes its successor.
  **Lemma 8.5.8** At any point in the procedure, any element of [h, t] that originally appeared in [f0’, l0) precedes f0.  Similarly, any element of [h, t] that originally appeared in [f1’, l1) precedes f1.
  **Proof.** We will prove this by showing that the claim holds initially, and that every block preserves this claim.
  Initially, h and t are uninitialized, so there is nothing to prove.
  The block { h = f1; advance_tail(t, f1); goto s1 } sets [h, t] to the singleton range containing f1’ and sets f1 to successor(f1’); since f1’ precedes successor(f1’), the claim holds.  Similarly, the block { h = f0; advance_tail(t, f0); goto s0 } sets [h, t] to the singleton range containing f0’ and sets f0 to successor(f0’); since f0’ precedes successor(f0’), the claim holds.
  Calling link_to_tail(t, f1) or advance_tail(t, f1) extends [h, t] by the element f1 and sets f1 to successor(f1).  By transitivity of the precedence relation and the fact that f1 precedes successor(f1), the claim still holds after one of these calls.  Similarly, calling link_to_tail(t, f0) or advance_tail(t, f0) extends [h, t] by the element f0 and sets f0 to successor(f0).  By transitivity of the precedence relation and the fact that f0 precedes successor(f0), the claim still holds after one of these calls.
  **Lemma 8.5.9** At any point in the procedure, if i precedes j in [h, t] and i, j both came from [f0’, l0), then i precedes j in [f0’, l0).  Similarly, at any point in the procedure, if i precedes j in [h, t] and i, j both came from [f1’, l1), then i precedes j in [f1’, l1).
  **Proof.** We will show that the claim is initially true, and that every statement preserves this claim.  Initially, h and t are uninitialized, so there is nothing to prove.  The blocks that start with h = f1 and h = f0 set [h, t] to a singleton range, so there is again nothing to prove.  Finally, by Lemma 8.5.8, any calls to advance_tail or link_to_tail preserve this claim.

Suppose i precedes j in [h, ll) immediately before the return statement in s2.  If i and j are both in [f1, l1) then Lemma 8.5.1 implies that i precedes j in [f1’, l1).  If i and j are both in [h, t], then Lemma 8.5.9 implies that i precedes j in [f1’, l1).  Finally, if i is in [h, t] and j is in [f1, l1), then by Lemma 8.5.1, Lemma 8.5.7, and transitivity of precedence, i precedes j in [f1’, l1).  Similarly, suppose i precedes j in [h, l0) immediately before the return statement in s3.  If i and j are both in [f0, l0) then Lemma 8.5.1 implies that i precedes j in [f0’, l0).  If i and j are both in [h, t], then Lemma 8.5.9 implies that i precedes j in [f0’, l0).  Finally, if i is in [h, t] and j is in [f0, l0), then by Lemma 8.5.1, Lemma 8.5.7, and transitivity of precedence, i precedes j in [f0’, l0).

We conclude that combine_linked_nonempty is a precedence-preserving link rearrangement.

**Lemma 8.6** If [f0, l0) and [f1, l1) are nonempty increasing bounded ranges, their merge with merge_linked_nonempty is an increasing bounded range.
**Proof.** We will proceed with another sequence of lemmas.
  **Lemma 8.6.1** Let f0’ be the original value of the argument f0 (i.e. before the procedure has performed any assignments to f0).  At the beginning of the label s0, t is an element of [f0’, l0), and at the beginning of the label s1, t is an element of [f1’, l1).
  **Proof.** Any ‘goto s0’ statement immediately follows either advance_tail(t, f0) or link_to_tail(t, f0); both advance_tail and link_to_tail, called with t as the first argument, have the effect of setting t to the second argument.  Lemma 8.5.1 implies that at any point in the procedure, f0 is an element of [f0’, l0), so the claim follows.  The case with s1 in place of s0 is handled analogously.
  **Lemma 8.6.2** If [f0, l0) and [f1, l1) are increasing, then in combine_linked_nonempty, [h, t] is always increasing.
  **Proof.** Above s0, either h and t are uninitialized, or [h, t] is a singleton, so there is nothing to prove.  Suppose [h, t] is increasing at the beginning of s0.  By Lemma 8.5.2, !r(f1, t), so link_to_tail(t, f1) will extend [h, t] by the element f1 and preserve the fact that [h, t] is increasing.  By Lemma 8.6.1, t is an element of [f0’, l0), and again by Lemma 8.5.2, successor(t) = f0; thus the assumption that [f0’, l0) is increasing implies that !r(f0, t), so advance_tail(t, f0) will extend [h, t] by the element f0 and preserve the fact that [h, t] is increasing.  Similarly, if [h, t] is increasing at the beginning of s0, then it is increasing at the end of s0.  No other statements in the procedure modify the range [h, t], so the proof is complete.
  **Lemma 8.6.3** If [f0, l0) and [f1, l1) are increasing, and if combine_linked_nonempty returns (h, t, l), then [h, l) is increasing.
  **Proof.** At the beginning of s2, [h, t] is increasing (by Lemma 8.6.2), t precedes f1 (by Lemma 8.5.7), and [f1, l1) is increasing (by Lemma 8.5.1 and the assumption that the [f1, l1) was increasing for the original value of f1).  We conclude that the combined range [h, l1) returned by the procedure is increasing.
  Similarly, at the beginning of s3, [h, t] is increasing (by Lemma 8.6.2), t precedes f0 (by Lemma 8.5.7), and [f0, l0) is increasing (by Lemma 8.5.1 and the assumption that the [f0, l0) was increasing for the original value of f0).  We conclude that the combined range [h, l0) returned by the procedure is increasing.
  **Lemma 8.6.4** If the preconditions to combine_linked_nonempty hold, and the procedure returns (h, t, l), then [h, l) is a bounded range.
  **Proof.** We will first show that any point in the procedure, if h and t are initialized then t = successor^j(h) for some nonnegative integer j.  Above the label s0, either h and t are uninitialized or h = t, so there is nothing to prove.  Let t0 be the value of t before a call to link_to_tail.  Then link_to_tail sets t to successor(t0), so after the link_to_tail call, t = successor^{j+1}(h).  Now let t0 be the value of t before a call to advance_tail; then Lemma 8.5.2 ensures that after the call, successor(t0) = t; thus after the advance_tail call, t = successor^{j+1}(h).
  Next, by Lemma 8.5.2, at the beginning of s2 we have l1 = successor^j(f0), so set_link(t, f1) along with the result of the previous paragraph shows that l1 = successor^k(h) for some nonnegative integer k.  Similarly, at the beginning of s3 we have l0 = successor^j(f0), so set_link(t, f0) along with the result of the previous paragraph shows that l0 = successor^k(h) for some nonnegative integer k.  We conclude that [h, l) is a bounded range.

Finally, Lemma 8.6.3, Lemma 8.6.4, and the definition of merge_linked_nonempty (which simply calls combine_linked_nonempty) shows that if the preconditions hold, then the result of the procedure is an increasing range.

**Lemma 8.7** If i0 in [f0, l0) and i1 in [f1, l1) are iterators whose values are equivalent under r, in the merge of these ranges with merge_linked_nonempty, i0 precedes i1.
**Proof.** Consider the relation r’ that holds for two iterators i, j whenever r(i, j) holds, and also holds if i and j are equivalent under r but i is an element of the range [f0, l0) and j is an element of the range [f1, l1).
  **Lemma 8.7.1** r’ is a weak ordering.
	We will first show that if r is a weak ordering and [f0, l0) and [f1, l1) are disjoint, then r’ is also a weak ordering.
  Let i, j, be iterators.  If i and j are both from [f0, l0) or both from [f1, l1), then weak-trichotomy of r implies weak-trichotomy of r’ for i and j.  If i is from [f0, l0) and j is from [f1, l1), weak-trichotomy of r implies that either r(i, j), in which case r’(i, j), r’(j, i), in which case r’(j, i), or i and j are equivalent under i, in which case r’(i, j).  By the assumption that [f0, l0) and [f1, l1) are disjoint, r’(j, i) does not hold, so weak-trichotomy holds.  The situation is analogous if i is from [f1, l1) and j is from [f0, l0).
  Next, let i, j, k be iterators.  If r’(i, j) then either r(i, j) or i and j are equivalent but i is from [f0, l0) and j is from [f1, l1).  If r’(j, k) then either r(j, k) or j and k are equivalent but j is from [f0, l0) and k is from [f1, l1).  We consider each combination:
  If r(i, j) and r(j, k), then transitivity of r implies r(i, k), and the definition of r’ implies r’(i, k).
  If r(i, j) and j and k are equivalent, then also r(i, k) holds (if i and k are equivalent, transitivity of equivalence would imply that j and i are equivalent, which would contradict weak-trichotomy of r; if r(k, i) then transitivity of r would imply r(k, j), which would again contradict weak-trichotomy of r), and r’(i, k) holds by definition of r’.
  Similarly, if i and j are equivalent and r(j, k), then by an analogous argument to the previous paragraph, r(i, k) holds, so by definition of r’, r’(i, k) holds.
  Finally, by the assumption that [f0, l0) and [f1, l1) are disjoint, if r’(i, j) and r’(j, k), it cannot be the case that i is equivalent to j under r and j is equivalent to k under r, because otherwise, j would be in both [f1, l1) and [f0, l0).
  **Lemma 8.7.2** Using r’ in place of r in combine_linked_nonempty produces the same result.
  **Proof.** combine_linked_nonempty only ever passes the arguments f1, f0 (in that order) to r.  By Lemma 8.5.1, f1 is an element of the original range [f1, l1) and f0 is an element of the original range [f0, l0).  If r(f1, f0) returns true, then r’(f1, f0) would also return true.  If r(f1, f0) returns false, then by weak-trichotomy either r(f0, f1) holds, in which case r’(f0, f1) holds and r’(f1, f0) would return false (by the weak-trichotomy proved in Lemma 8.7.1), or r(f0, f1) does not hold, in which case f0 and f1 are equivalent under r, r’(f0, f1) holds, and r’(f1, f0) would return false.  Thus we have proved that r(f1, f0) returns true if and only if r’(f1, f0) returns true.

Finally, if i0 is an element of [f0, l0), i1 is an element of [f1, l1), and i1 precedes i0 in the output of merge_linked_nonempty, then by Lemma 8.7.2, i1 would also precede i0 in the output of merge_linked_nonempty called with r’ in place of r.  But this would contradict Lemma 8.6, because r’(i0, i1), so the output of merge_linked_nonempty would not be an increasing range.  We conclude that i0 precedes i1 in the output of merge_linked_nonempty.

**Lemma 8.8** sort_linked_nonempty_n is a link rearrangement.
**Proof.** We begin with the following lemma:
  **Lemma 8.8.1** Provided that set_link does not change any iterator values, merge_linked_nonempty is a link rearrangement.
  **Proof.** The fact that the input ranges are disjoint is a precondition of the procedure.  Since there is only one output range, the output ranges are trivially disjoint.  Let t.m2 = successor^j(t.m0); by the precondition that the input ranges are nonempty, we have j > 0.  Thus find_last(t.m1, t.m2) returns the element whose successor is t.m2, i.e. successor^{j-1}(t.m0), and then establishes successor(successor^{j-1}(t.m0)) = l1.  But then [t.m0, l1) consists of the elements t.m0, successor(t.m0), …, successor{j-1}(t.m0), and these are precisely the same elements as [t.m0, t.m2).  Together with Lemma 8.5, this implies that the set of iterators in the input and output ranges are the same.  We assumed that set_link does not change any iterator values; finally, Lemma 8.5 shows that combine_linked_nonempty does not change any iterators’ values either, so the last condition holds.
  **Lemma 8.8.2** The limit of the range returned by sort_linked_nonempty_n is precisely the limit of the input range, i.e. successor^n(f).
  **Proof.** We proceed by induction on n.  If n == 1, then the returned limit is successor(f), and there is nothing to prove.  Otherwise, by our inductive hypothesis, the limit of the range returned by the first recursive call is successor^h(f).  sort_linked_nonempty_n only rearranges links in its input range, and since none of successor^h(f), …, successor^n(f) were in the input range to the first recursive call, these elements are precisely the range [[successor^h(f), n - h)).  Applying our inductive hypothesis again, the limit of the range returned by the second recursive call is successor^{n-h}(successor^(f)), i.e. successor^n(f).  Finally, since successor^n(f) is the fourth argument to the call to merge_linked_nonempty, and the last step of merge_linked_nonempty is to set its limit to the value of its fourth argument, we conclude that the limit returned by sort_linked_nonempty_n is successor^n(f).

We will now proceed with Lemma 8.8.  Since there is only one input range and one output range, disjointness of input and output ranges is trivial.  For the remaining conditions, we will proceed by induction on n.  If n == 1, then the output is the same as the input, so there is nothing to prove.  Suppose n > 1, and the claim is true for m < n.  Then the claim is true for both h and n - h (when n > 1, we have half_nonnegative(n) >= 1).  Thus both recursive calls to sort_linked_nonempty_n are link rearrangements.  Furthermore, by Lemma 8.8.1, the call to merge_linked_nonempty is also a link rearrangement.

Suppose i appears in [[f, h|).  Then i appears in [p0.first, p0.second), and i appears in the returned range of merge_linked_nonempty.

Suppose i appears in [successor^h(f), successor^n(f)).  By Lemma 8.8.2, p0.m1 = successor^h(f), so [[p0.m1, n - h|) = [successor^h(f), successor^n(f)); thus then i appears in [p1.first, p1.second), and i appears in the returned range of merge_linked_nonempty.

In the other direction, suppose i appears in the output range of merge_linked_nonempty.  Then i appears in the output range of one of the two recursive calls to sort_linked_nonempty, so i appears in the input range of one of the two recursive calls to sort_linked_nonempty, so i appears in either [[f, h|) or [successor^h(f), successor^n(f)), and i appears in [[f, n|).

Finally, since neither of the two recursive calls nor the call to merge_linked_nonempty change the values of any iterators in the input range, the entire procedure does not change the values of any iterators in the input range, and we conclude that sort_linked_nonempty_n is a link rearrangement.

**Lemma 8.9** If [[f, n|) is a nonempty counted range, sort_linked_nonempty_n will rearrange it into an increasing bounded range.
**Proof.** We will proceed by induction on n.  If n == 1 then the input range is trivially an increasing bounded range, sort_linked_nonempty_n returns its input, and there is nothing more to prove.  Suppose n > 1 and the claim holds for all m < n.  By our inductive hypothesis, the two recursive calls turn [p0.m0, p0.m1) and [p1.m0, p1.m1) into increasing bounded ranges, and since Lemma 8.8 shows that sort_linked_nonempty_n is a link rearrangement, disjointness of [[f, h|) and [[p0.m1, n - h|) = [[successor^h(f), n - h|) (this equality follows by Lemma 8.8.2) shows that [p0.m0, p0.m1) and [p1.m0, p1.m1) are disjoint.  Finally, Lemma 8.6 shows that the output of merge_linked_nonempty is an increasing bounded range.

**Lemma 8.10** sort_linked_nonempty_n is stable with respect to the supplied weak ordering r.
**Proof.** We will begin with the following:
  **Lemma 8.10.1** merge_linked_nonempty is precedence-preserving.
  **Proof.** The proof of Lemma 8.8.1 shows that after the statement set_link(find_last(t.m1, t.m2), l1), [t.m0, l1) is identical to the range returned by combine_linked_nonempty.  Thus the fact that merge_linked_nonempty is precedence-preserving follows immediately from the fact that combine_linked_nonempty is precedence-preserving, and we established the latter in Lemma 8.5.

For Lemma 8.10, we will proceed by induction on n.  If n == 1 then there are no precedence relations in the input and output ranges, and thus nothing to prove.  Suppose n > 1 and the claim holds for all m < n.  Suppose i and j have equivalent values under r, and that i precedes j in the input range.  If i and j are both in [[f, h|) or both in [[p.m1, n - h|)  then the claim follows from the inductive hypothesis, which implies that i precedes j in the output range of the recursive call to sort_linked_nonempty_n, and from Lemma 8.10.1, which implies that i precedes j in the output range of merge_linked_nonempty, which is the same as the output range of the entire procedure.  If i appears in [[f, h|) and j appears in [[p.m1, n - h|) (the other way around is impossible since every element in the former range precedes every element in the latter range), then since sort_linked_nonempty_n is a link rearrangement, i appears in [p0.m0, p0.m1), j appears in [p1.m0, p1.m1), and Lemma 8.7 implies that i precedes j in the output of merge_linked_nonempty, i.e. the output of the entire procedure.

**Lemma 8.A** Suppose the trees rooted at curr and prev are disjoint.  Let n = weight(curr) and let c, p be the original values of curr, prev.  Then:
    (a) The next 3n calls to tree_rotate will not modify the tree rooted at p
    (b) After 3n calls, we will have prev = c, curr = p
    (c) At no point before 3n calls will we have curr equal to any descendants of p
**Proof.** We proceed by induction.

If n = 1, then the claim follows immediately from the definition of tree_rotate.

If n > 1, we will use the notation (a, c, b) to denote a coordinate c whose left successor is a and whose right successor is b.  Let c and p be the original values of curr and prev, and let l and r be the original left and right successors of c.

After one call to tree_rotate, curr = l and prev = (r, c, p).  Let n_l = weight(l).  Since the tree rooted at l is disjoint from the tree rooted at (r, c, p), by the inductive hypothesis the next 3n_l calls to tree_rotate will not modify the tree rooted at (r, c, p) (in particular, it will not modify the tree rooted at p), and after 3n_l calls to tree_rotate we will have curr = (r, c, p) and prev = l.  Furthermore, at no point before 3n_l calls will we have curr equal to any descendants of c (in particular, at no point before 3n_l calls will we have curr equal to p).

After one more call to tree_rotate, we will have curr = r and prev = (p, c, l).  Let n_r = weight(r).  Since the tree rooted at r is disjoint from the tree rooted at (p, c, l), by the inductive hypothesis the next 3n_r calls to tree_rotate will not modify the tree rooted at (p, c, l) (in particular, it will not modify the tree rooted at p), and after 3n_r calls to tree_rotate we will have curr = (p, c, l) and prev = r.  Furthermore, at no point before 3n_r calls will we have curr equal to any descendants of c (in particular, at no point before 3n_r calls will we have curr equal to p).

Finally, one more call will set curr = p and prev = (l, c, r); thus after 1 + 3n_l + 1 + 3n_r + 1 = 3(1 + n_l + n_r) = 3n calls to tree_rotate, the tree rooted at p was not modified at any point, curr is equal to the original value of prev and prev is equal to the original value of curr.

**Lemma 8.B** Let c and p be the initial values of curr and prev, let l and r be the initial left and right successors of c, and let n, n_l, n_r be the weights of the trees rooted at c, l, r.  Then:

(a) Upon repeated calls to tree_rotate(curr, prev), the left and right successors of c will go through three transitions: (l, r) -> (r, p) -> (p, l) -> (l, r)
(b) The second and third transitions take 3n_l + 1 and 3n_r + 1 calls, respectively
(c) If p was empty, then 3n calls will restore the original values of curr and prev

**Proof.** Let n be the weight of c; we will proceed by induction on n.

If n = 1, the claim follows immediately by the definition of tree_rotate.

Suppose n > 1 and the claim is true for m < n.  One call will set curr = l, prev = (r, c, p), which completes the first transition.

By Lemma 8.A, 3n_l more calls will set curr = (r, c, p), prev = l without modifying the tree rooted at (r, c, p), and one more call will set curr = r and prev = (p, c, l), which completes the second transition after 3n_l + 1 calls.  Note that Lemma 8.A(c) implies that no fewer than 3n_l calls after curr = l, prev = (r, c, p) holds, will cause curr == c to hold.

Again by Lemma 8.3, 3n_r more calls will set curr = (p, c, l), prev = r without modifying the tree rooted at (p, c, l).  Note that Lemma 8.A(c) implies that no fewer than 3n_r calls after curr = r, prev = (p, c, l) holds, will cause curr == c to hold.  If p is empty, then one more call will set curr = (l, c, r) and prev = p.  Otherwise, one more call will set curr = p and prev = (l, c, r).  Either way, this completes the third transition after 3n_r + 1 calls, which proves (a) and (b).  In the case where p was empty, the original values of curr and prev were restored after a total of 3(n_l + n_r + 1) = 3n calls, which proves (c).

**Lemma 8.C** Let c and p be the initial values of curr and prev, and let n = weight(c).  If i is a non-empty descendant of c with weight n_i, then repeated calls to tree_rotate(curr, prev) will set curr = i within 3(n - n_i) calls.
**Proof.** We proceed by induction on n.

If n = 1, then c is its only non-empty descendant, and the claim trivially holds.

Suppose n > 1 and the claim holds for m < n.  If i = c there is nothing to prove.  Let l and r be the left and right successors of c, and let n_l, n_r be the weights of the corresponding subtrees.

If i != c and i is reachable from l, then one call to tree_rotate will set curr to l, and by the inductive hypothesis, fewer than 3n_l additional calls will set curr to i, for a total of at most 1 + 3(n_l - n_i) calls (which is less than 3(n - n_i)).

If i != c and i is reachable from r, then one call to tree_rotate will set curr to l and prev to (r, c, p).  By Lemma 8.A(b), 3n_l additional calls to tree_rotate will set curr to (r, c, p) and prev to l.  One more call will set curr to r and prev to (p, c, l).  By the inductive hypothesis, fewer than 3(n_r - n_i) additional calls will result in curr = i, for a total of at most 2 + 3n_l + 3n_r - 3n_i calls (which is less than 3(n - n_i)).

**Theorem 8.1** Consider a call of traverse_rotating(c, proc) and any non-empty descendant i of c, where i has initial left and right successors l and r and predecessor p.  Then:

(1) The left and right successors of i go through three transitions (l, r) -> (r, p) -> (p, l) -> (l, r).
**Proof.** If i = c then claim follows from Lemma 8.B(a), which shows that the transitions will occur after sufficiently many calls to tree_rotate, from the definition of tree_rotate, which shows that the first transition will occur after a single call to tree_rotate, and from Lemmas 8.A(c) and 8.B(b), which shows that last two transitions will occur before before traverse_rotating terminates.

If i != c, then let n = weight(c) and n_i = weight(i).  Lemma 8.C implies that curr = i will hold within 3(n - n_i) calls to tree_rotate, Lemmas 8.A(c) and 8.B(b) together imply that traverse_rotating will not terminate until 3n calls to tree_rotate, and another application of Lemma 8.B(b) together with the definition of tree_rotate (which shows that the first transition occurs after a single call) shows that the three transitions on the left and right successors of i will occur within 3n_i calls of curr becoming i.  Thus we conclude that the three transitions will occur within 3(n - n_i) + 3n_i = 3n calls, i.e. they will occur before traverse_rotating terminates.

(2) If n_l and n_r are the weights of l and r, the transitions (r, p) -> (p, l) and (p, l) -> (l, r) take 3n_l + 1 and 3n_r + 1 calls of tree_rotate, respectively.
**Proof.** Note that tree_rotate only modifies successors of curr, thus no transitions can occur for i before curr becomes i.  As soon as curr becomes i within traverse_rotating (which must happen by Lemma 8.C), we can apply Lemma 8.B(b) to show that the transitions take precisely 3n_l + 1 and 3n_r + 1 calls to tree_rotate.

(3) If k is a running count of the calls of tree_rotate, the value of k mod 3 is distinct for each of the three transitions of the successors of i.
**Proof.** Let j be the count when curr = i first occurs.  The first transition will occur at count j + 1 (this follows immediately from the definition of tree_rotate), the second transition will occur at count j + 3n_i + 2, and the third transition will occur at count j + 3n_i + 3 (these follow immediately from (2) above).  Thus the counts are congruent to j, j + 1, and j + 2 (mod 3), which are distinct mod 3 (none of their differences are divisible by 3).

(4) During the call of traverse_rotating(c, proc), the total number of calls of tree_rotate is 3n, where n is the weight of c.
**Proof.** The proof of Lemma 8.B(b) shows that curr == c will not hold after 1, ..., 3n_l calls, will hold after 3n_l + 1 calls (at which point the first do... while loop will terminate) , will not hold after 3n_l + 2, ..., 3n_l + 3n_r + 1 calls, and will hold and after 3n_l + 3n_r + 2 calls (at which point the second do... while loop will terminate).  Finally, the procedure makes one more call, for a total of 3n_l + 3n_r + 3 = 3n calls.

**Lemma 9.1** If the sizes of the input ranges are n_0 and n_1, my_merge_copy and my_merge_copy_backward perform n_0 + n_1 assignments and, in the worst case, n_0 + n_1 - 1 comparisons.
**Proof.**
  **Lemma 9.1.1** If l_i - f_i == n when my_copy is about to enter an iteration of the while loop, then my_copy performs n more assignments before returning.
  **Proof.** We proceed by induction.  If n == 0, then f_i == l_i, so my_copy returns immediately.  If n > 0 then f_i != l_i, so my_copy calls my_copy_step, performs one assignment, and sets f_i to successor(f_i).  At this point, my_copy is about to enter another iteration of the while loop, but the new value of f_i satisfies l_i - f_i == n - 1; thus the claim holds by our inductive hypothesis.
  **Lemma 9.1.2** If l_i - f_i == n for a given call to my_copy, then my_copy performs n assignments before returning.
  **Proof.** This follows from Lemma 9.1.1 and the fact that my_copy starts with the while loop.
  **Lemma 9.1.3** If l_i0 - f_i0 == n0 and l_i1 - f_i1 == n1 when my_combine_copy is about to enter an iteration of the while loop, then my_combine_copy performs n0 + n1 assignments before returning.
  **Proof.** We proceed by induction on n0 + n1.
  If n0 + n1 == 0, then n0 == n1 == 0 and f_i0 != l_i0 and f_i1 != l_i1 both fail, so the body of the while loop does not executed.  Lemma 9.1.2 implies that both calls to my_copy perform no assignments,  so in the case n0 + n1 == 0, my_combine_copy returns without performing any assignments.
  Suppose n0 + n1 > 0 and n0 == 0.  Then f_i0 != l_i0 fails, so the body of the while loop does not get executed.  Lemma 9.1.2 implies that the first call to my_copy, with [f_i0, l_i0) as the input range, performs no assignments, and the second call to my_copy, with [f_i1, l_i1) as the input range, performs n1 assignments, so our claim holds in this case.
  Similarly, if n0 + n1 > 0 and n1 == 0, then my_combine_copy returns after performing n0 assignments, as claimed.
  Finally, suppose n0 + n1 > 0, n0 > 0, and n1 > 0 all hold.  Whether or not r(f_i1, f_i0) holds, my_combine_copy calls my_copy_step, which performs one assignment and sets either f_i0 or f_i1 to its successor.  At this point, my_combine_copy is about to enter another iteration of the while loop, with the quantity n0 + n1 decreased by one (as compared to the previious iteration); thus by our inductive hypothesis, my_combine_copy performs a total of 1 + (n0 + n1 - 1) = n0 + n1 assignments.
  **Lemma 9.1.4** If [f_i0, l_i0) and [f_i1, l_i1) are the input ranges to my_combine_copy, where l_i0 - f_i0 == n0 and l_i1 - f_i1 == n1, then my_combine_copy performs n0 + n1 assignments before returning.
  **Proof.** This follows from Lemma 9.1.3 and the fact that my_combine_copy starts with the while loop.
  **Lemma 9.1.5** If l_i0 - f_i0 == n0 and l_i1 - f_i1 == n1 when my_combine_copy is about to enter an iteration of the while loop, then my_combine_copy performs at most n0 + n1 - 1 comparisons before returning.
  **Proof.** We will proceed by induction on n0 + n1.
  If n0 + n1 == 0, then the body the while loop does not get executed, and since my_copy does not perform any comparisons, my_combine_copy returns without performing any comparisons.
  If n0 + n1 > 0 and n0 == 0, then again the body of the while loop does not get executed, so my_combine_copy returns without performing any comparisons, i.e. the claim holds in this case (note that n0 + n1 > 0 implies n0 + n1 - 1 >= 0).  Similarly, the claim also holds in the case where n0 + n1 > 0 and n1 == 0.
  Now suppose n0 + n1 > 0, n0 > 0, and n1 > 0.  Then my_combine_copy will perform one comparison and then call my_copy_step, which performs no comparisons but sets either f_l0 or f_l1 to its successor.  At this point, my_combine_copy is about to enter another iteration of the while loop, with the quantity n0 + n1 decreased by one since the previous iteration; thus by our inductive hypothesis, my_combine_copy performs at most 1 + (n0 + n1 - 1) - 1 = n0 + n1 - 1 comparisons.
  **Lemma 9.1.6** If [f_i0, l_i0) and [f_i1, l_i1) are the input ranges to my_combine_copy, where l_i0 - f_i0 == n0 and l_i1 - f_i1 == n1, then my_combine_copy performs at most n0 + n1 - 1 comparisons before returning.
  **Proof.** This follows from Lemma 9.1.5 and the fact that my_combine_copy starts with the while loop.

Finally, to prove Lemma 9.1, note that the only step in my_merge_copy is to call my_combine_copy with the same input and output ranges; thus Lemma 9.1.4 and Lemma 9.1.6 imply Lemma 9.1 for my_merge_copy.  The case of my_merge_copy_backward is handled analogously.

Note that given n0 > 0 and n1 > 0, there always exists input ranges that produce this worst-case behavior.  Consider the ranges [f_i0, l_i0) and [f_i1, l_i1), let t_i0 be the final elements of the first range, and suppose the following conditions hold:

    (1) !r(f_i1, k_i0) holds for every element k_i0 of [f_i0, l_i0) except t_i0
    (2) r(k_i1, t_i0) holds for every element k_i1 of [f_i1, l_i1)

Each of the first n0 - 1 iterations of the while loop will perform a comparison and then set f_i0 to its successor, at which point f_i0 will have advanced to t_i0.  Each of the next n1 iterations of the while loop will perform a comparison and then set f_i1 to its successor, at which point f_i1 will have advanced to l_i1; my_combine_copy will then make two calls to my_copy (neither of which perform any comparisons) and then return, after having made a total of n0 + n1 - 1 comparisons.

**Lemma 9.A** my_combine_copy performs at least min(n0, n1) comparisons.
**Proof.** Each iteration of the while loop decreases min(n0, n1) by at most one, and since the termination condition of the while loop is equivalent to the condition min(n0, n1) == 0, my_combine_copy must perform at least min(n0, n1) iterations of the while loop.  Furthermore, each iteration of the while loop perform one comparison, so the claim follows.

Note that there always exist input ranges of size n0, n1 that produce this best-case behavior.  If either n0 == 0 or n1 == 0, then every input range causes my_combine_copy to return without any comparisons.  If n0 > 0 and n1 > 0 and n0 < n1, then take any input ranges such that for any k_i0 in [f_i0, l_i0) and k_i1 in [f_i1, l_i1), !r(k_i1, k_i0) holds.  Then the first n0 iterations of the while loop will increment f_i0, at which point f_i0 == l_i0 will hold, and my_combine_copy will return having performed n0 comparisons.  Similarly, if n1 < n0, then take any ranges such that for any k_i0 in [f_i0, l_i0) and k_i1 in [f_i1, l_i1), r(k_i1, k_i0) holds.

**Lemma 9.B** The stated postconditions of exchange_values(x, y) hold.
**Proof.** Suppose z0 == source(i) and z1 == source(j) before exchange_values was called.  Regularity of ValueType(I0) implies that after the assignment ValueType(I0) t = source(x), z0 and t are equal.  Next, regularity of ValueType(I0) and the definition of Mutable, i.e. the fact that aliased(x, x) holds, shows that the assignment sink(x) = source(y) establishes z1 == source(i).  Finally, another application of regularity and the definition of Mutable implies that after the assignment sink(y) = t, z0 == source(j) holds.

**Lemma 9.2** The effects of exchange_values(i, j) and exchange_values(j, i) are equivalent.
**Proof.** We begin by swapping x and y in the body of exchange_values:

    ValueType(I0) t = source(y);
            sink(y) = source(x);
            sink(x) = t;

We introduce another temporary variable (regularity implies that this does not change the result):

    ValueType(I0) t = source(y);
    ValueType(I0) u = source(x);
             sink(y) = u;
             sink(x) = t;

Since the first line does not affect u or x and the second line does not affect t or y, we can swap them without affecting the result.  By a similar argument, we can swap the third and fourth lines:

    ValueType(I0) u = source(x);
    ValueType(I0) t = source(y);
            sink(x) = t;
            sink(y) = u;

Renaming the temporary variables u and t have no effect on the result:

    ValueType(I0) t = source(x);
    ValueType(I0) u = source(y);
            sink(x) = u;
            sink(y) = t;

Finally, again by regularity, we can remove the temporary variable u without changing the result:

    ValueType(I0) t = source(x);
            sink(x) = source(y);
            sink(y) = t;

But this is precisely the original definition of exchange_values, before we swapped x and y; thus we conclude that swapping x and y in the body of exchange_values does not affect the result.

**Lemma 10.1** A transformation on a finite definition space is an onto transformation if and only if it is both an into and a one-to-one transformation.
**Proof.** Let f be a transformation, and let X = {x_1, ..., x_n} be the finite definition space of f.

Suppose f is not into.  Then there exists some x_i in X such that f(x_i) is not in X.  But then the remaining n - 1 elements of X can map to at most n - 1 different elements of X, so f is not onto.

Similarly, suppose f is not one-to-one.  Then there exist distinct x_i, x_j in X such that f(x_i) = f(x_j).  But then x_i, x_j, and the remaining n - 2 elements of X can map to at most n - 1 different elements of X, so f is not onto.

By taking the contrapositive of the two results above, it follows that if f is an onto transformation on a finite definition space, then f is both into and one-to-one.

Conversely, if f is one-to-one, then the elements f(x_1), ..., f(x_n) are all distinct.  Furthermore, if f is also into, then each f(x_1), ..., f(x_n) appears in X.  But X has exactly n  elements, so every element of X must appear among f(x_1), ..., f(x_n), which shows that f is onto.

**Lemma 10.2** The composition of permutations is a permutation.
**Proof.** Let q, p be permutations on X.  We will show that q o p is onto.  Suppose z is an arbitrary element of X; since q is onto, there exists some y such that q(y) = z.  Since p is onto, there exists some x such that p(x) = y.  Thus q o p(x) = z, which shows that q o p is a permutation.

**Lemma 10.3** Composition of permutations is associative.
**Proof.** Let p, q, r be permutations on X, and let x be an arbitrary element of x.  Then

    p o (q o r)(x) = p(q o r(x))
                   = p(q(r(x))
                   = (p o q)(r(x))
                   = (p o q) o r(x)

which proves associativity of composition.

**Lemma 10.4** For every permutation p on a set S, there is an inverse permutation p^-1 such that p^-1 o p = p o p^-1 = identity_S.
**Proof.** Let q be function that maps x to whatever element y in S satisfies p(y) = x.  Such a y exists because p is onto, and Lemma 10.1 implies that p is one-to-one, i.e. there is exactly one such y in S.  Thus q is well-defined.  Let z be an arbitrary element of S.  Lemma 10.1 implies that p is into, so p(z) = w for some w in S, and by definition, we have q(w) = z.  Thus q is onto, i.e. a permutation.

Let z be an arbitrary element of S, and suppose p(z) = w.  Then by definition of q, q(w) = z.  Thus q o p(z) = z, so q o p = identity_S.

Let w be an arbitrary element of S, and suppose q(w) = z.  Then by definition of w, p(z) = w.  Thus p o q(w) = w, so p o q = identity_S.

Taking q = p^-1 completes the proof.

**Lemma 10.5** Every finite group is [isomorphic to] a subgroup of the permutation group of its elements, where every permutation in the subgroup is generated by multiplying all the elements by an individual element.
**Proof.** Let G be a finite group, let x be an arbitrary element of G, and let e be the identity element of G.
  **Lemma 10.5.1** The transformation p_x that maps g to x * g is a permutation of G.
  **Proof.** Let h be an arbitrary element of G.  Then since x has an inverse and  * is associative, p_x(x^-1 * h) = x * (x^-1 * h) = (x * x^-1) * h = e * h = h.
  **Lemma 10.5.2** If x != x', then the transformations p_x and p_x' are distinct permutations of G.
  **Proof.** p_x maps e to x, but p_x' maps e to x'.
  **Lemma 10.5.3** The map f that sends x to p_x is a group homomorphism (multiplication in the domain becomes composition in the codomain).
  **Proof.** Let z = x * y.  Then p_z is the transformation that maps g to x * y * g.  But we also have p_x o p_y(g) = p_x(p_y(g)) = p_x(y * g) = x * y * g; thus f(x * y) = f(x) o f(y).
  **Lemma 10.5.4** The image of G under f is a subgroup of the set of permutations of G.
  **Proof.** The image of any group homomorphism is a subgroup of the codomain.
  **Lemma 10.5.5** f is a group isomorphism from G to f(G).
  **Proof.** Lemma 10.5.3 shows that f is a group homomorphism.  Clearly, f is onto.  Lemma 10.5.2 shows that f is also one-to-one, so f is a bijective group homomorphism, i.e. a group isomorphism.

Lemma 10.5.4 and Lemma 10.5.5 together show that G is isomorphic to a subgroup of the permutation group of G.

**Lemma 10.6** Every element in a permutation p belongs to a unique cycle.
**Proof.** Let X be the definition space of p.  Since X is finite, there are no infinite orbits.  Since p is into (Lemma 10.1), there are no terminating orbits.  Thus we must have x^m = x^n for some m < n.  If m = 0 then x = x^n.  Either way, the orbit of x is circular, so x belongs to a cycle.

Suppose x is in the circular orbits of both y and z.  Then there exists m0, n0 such that p^m0(y) = x, p^n0(z) = x.  Since the orbits are circular, there also exists m1, n1 such that p^m1(x) = y, p^n1(x) = z.  But then p^{n1+m0}(y) = z and p^{m1+n0}(z) = y, so the circular orbits of y and z are identical.  Thus x belongs to a unique cycle C.

**Lemma 10.7** Any permutation of a set with n elements contains k <= n cycles.
**Proof.** Suppose a permutation had more than n cycles.  Each cycle must contain at least one element, and by Lemma 10.6, no two cycles can have an element in common, so there would be more than n elements being permuted.  We conclude that a permutation with a set of n elements contains at most n cycles.

**Lemma 10.8** Disjoint cyclic permutations commute (i.e. cyclic permutations whose cycles are disjoint).
**Proof.** Let p, q be cyclic permutations on S, and let C, D be their nontrivial cycles.
  **Lemma 10.8.1** For any x in S \ C, p(x) = x.
  **Proof.** Suppose not; then the orbit of x would be a nontrivial cycle of p distinct from C, which contradicts that p is a cyclic permutation.
If x is neither in C nor D, then p o q(x) = q o p(x) = x.  If x is in C, then neither x nor p(x) are in D, so q(x) = x and q(p(x)) = p(x).  Thus p o q(x) = p(x) and q o p(x) = p(x).  Finally, if x is in D, then neither x nor q(x) are in C, so p(x) = x and p(q(x)) = q(x).  Thus q o p(x) = q(x) and p o q(x) = q(x).

**Lemma 10.9** Every permutation can be represented as a product of the cyclic permutations corresponding to its cycles.
**Proof.** Let p be a permutation on S, and let C be a cycle of p.  Let p_C be the map defined as follows:

    p_C(x) = p(x) if x is in C
             x    otherwise

To see that p_C is a permutation, note that for any y in C there exists some x in C such that p(x) = y, i.e. p_C(x) = y, and for any y in S \ C p_C(y) = y.  To see that p_C is cyclic, note that for any element x not in C, the orbit of x under p_C is trivial, i.e. p_C has at most one nontrivial cycle (C may or may not be trivial).

Let C_1, ..., C_k be the nontrivial cycles of p; we will show that p_C_1 o ... o p_C_k = p (if p has no nontrivial cycles, we take the empty product to be the identity permutation).  Let x be an arbitrary element of S.  By Lemma 10.6, x belongs to a unique cycle C_i; thus by definition, p_C_i(x) = p(x), and for any j != i, p_C_j(x) = x and p_C_j(p(x)) = p(x); it follows that p_C_1 o ... o p_C_k(x) = p(x).

**Lemma 10.10** The inverse of a permutation is the product of the inverses of all of its cycles.
**Proof.**
  **Lemma 10.10.1** p and p^-1 have the same cycles.
  **Proof.** Suppose x is in some cycle C of p, and let y be in the orbit of x under p.  Since the orbit of x is circular, we can find some m such that p^m(y) = x.  Thus (p^-1)^m(x) = y, so y is also in the orbit of x under p^-1.  Conversely, suppose y in some cycle C of p^-1, and let x be in the orbit of y under p^-1.  Since the orbit of y is circular, we can find some n such that (p^-1)^n(x) = y.  Thus p^n(y) = x, so x is also in the orbit of y under p.
  **Corollary 10.10.2** The inverse of a cyclic permutation is cyclic.
  **Proof.** This follows directly from Lemma 10.10.1.

Let p be an arbitrary permutation, and let C_1, ..., C_k be its nontrivial cycles.  Then by Lemma 10.9, p o (p_C_1^-1 o ... o p_C_k^-1) = (p_C_1 o ... o p_C_k) o (p_C_1^-1 o ... o p_C_k^-1).    Using the the commutativity guaranteed by Lemma 10.8, this expression becomes (p_C_1 o p_C_1^-1) o ... o (p_C_k o p_C_k^-1), which is the identity permutation.  The same result holds if we multiply p by the product of the inverses of its cycles on the left, instead of on the right, so we conclude the inverse of p is equal to the product of the inverses of its cycles.

**Lemma 10.11** Every cyclic permutation is a product of transpositions.
**Proof.** Let p be a cyclic permutation on S, and let C be the corresponding cycle.  If |C| = 2 then p is a transposition, so the claim trivially holds.  Suppose |C| > 2, and choose any element y0 in C.  Since p is onto, there is some x0 such that p(x0) = y0.  Consider the map p' defined as follows:

    p'(x0) = p(y0)
    p'(y0) = y0    
    p'(x)  = p(x) if x != x0 ^ x != y0

We will first show that p' is onto.  Choose any y in S.  Since p is onto, there exists x in S such that p(x) = y.  If x = x0, then y = p(x0) = y0, so p'(y0) = y0 = y.  If x = y0, then y = p(x) = p(y0), so p'(x0) = p(y0) = y.  Otherwise, p'(x) = p(x) = y.

Next, we will show that p' is cyclic with cycle size |C| - 1.

Choose any x in S; if x is not in C, then x != x0 and x != y0, so p'(x) = p(x) = x; furthermore, p'(y0) = y0, so every element in a nontrivial cycle of p' must be an element of C \ {y0}.

Now choose any x, y in C \ {y0}.  We will show that x and y are in the same cycle under p'.

Let n be the smallest nonnegative integer such that y = p^n(x).  We will prove by induction on n that there exists some nonnegative integer m such that y = p'^m(x).
    If n = 0 there is nothing to prove.
    If n = 1, then we must have x != x0 (otherwise y = p(x0) = y0), and since we also have x != y0, p'(x) = p(x) = y.
    If n > 1, then consider the following cases:
        (1) p^{n-1}(x) = x0: this case is impossible because it would imply p^n(x) = y0 = y, which contradicts that y is in C \ {y0}.
        (2) p^{n-1}(x) = y0: then p^{n-2}(x) = x0.  By our inductive hypothesis, we can find some m such that x0 = p'^m(x); thus p'^{m+1}(x) = p'(x0) = p(y0) = p^n(x).
        (3) p^{n-1}(x) != x0 ^ p^{n-1}(x) != y0; then by our inductive hypothesis, we can find some m such that p^{n-1}(x) = p'^m(x), so p'^{m+1}(x) = p^n(x) = y.

Thus p' is cyclic with cycle size |C| - 1, and the cycle of p' is precisely C \ {y0}.

Finally, let t be the transposition that swaps x0 and y0.  We will show that p = p' o t.  Consider the following cases:
    (1) p' o t(y0) = p'(x0) = p(y0)
    (2) p' o t(x0) = p'(y0) = y0 = p(x0)
    (3) If x != y0 ^ x != x0, then p' o t(x) = p'(x) = p(x)
We conclude that for all x in S, p' o t(x) = p(x).  By our inductive hypothesis, p' is a product of transpositions; we conclude that p is the product of transpositions.

**Lemma 10.12** Every permutation is a product of transpositions.
**Proof.** This follows immediately from Lemma 10.9 (every permutation is a product of cyclic permutations), Lemma 10.11 (every cyclic permutation is a product of transpositions), and associativity of composition.

**Lemma 10.A** choose_S and index_S are bijections.
**Proof.** Let x be an arbitrary element of S.  Then choose_S(index_S(x)) = x, so choose_S is a surjection.  Similarly, if i is an arbitrary element of [0, n), then index_S(choose_S(i)) = i, so index_S is a surjection.

Next, suppose choose_S(i) = choose_S(j).  Then by definition of index_S together with its regularity, i = index_S(choose_S(i)) = index_S(choose_S(j)) = j, so choose_S is an injection.  Similarly, if index_S(x) = index_S(y), then by definition of choose_S together with its regularity, x = choose_S(index_S(x)) = choose_S(index_S(y)) = y, so index_S is an injection.

**Lemma 10.13** Let p be a permutation on a finite set S of size  n, and let p' be the permutation on [0, n) given by p'(i) = index_S(p(choose_S(i))).  Then p(x) = choose_S(p'(index_S(x))).
**Proof.** By definition of index_S together with its regularity, index_S(p(x) = index_S(choose_S(p'(index_S(x)))) = p'(index_S(x)).  By definition of choose_S together with its regularity, choose_S(p'(index_S(x))) = choose_S(index_S(p(x))) =  p(x).

**Lemma 10.B** Let p, p' be defined as above; then p'^2(i) = index_S(p^2(choose_S(i)) and p^2(x) = choose_S(p'^2(index_S(x)).
**Proof.** p'^2(i) = index_S(p(choose_S(index_S(p(choose_S(i)))))) = index_S(p(p(choose_S(i)))) = index_S(p^2(choose_S(i))).  Similarly, p^2(x) = choose_S(p'(index_S(choose_S(p'(index_S(x)))))) = choose_S(p'(p'(index_S(x)))) = choose_S(p'^2(choose_S(i))).

**Lemma 10.C** p^n(x) = y if and only if p'^n(index_S(x)) = index_S(y).
**Proof.** By induction.

Consider the case n = 0.  If x = y, then index_S(x) = index_S(y), and if index_S(x) and index_S(y), Lemma 10.A implies that x = y.

Now suppose n > 0 and the claim holds for n - 1.  Suppose p^n(x) = y; then p^{n-1}(p(x)) = p(y), so p'^{n-1}(index_S(p(x))) = index_S(y).

Conversely, suppose p'^n(index_S(x)) = index_S(y).  Then p'^{n-1}(p'(index_S(x))) = p'^{n-1}(index_S(p(choose_S(index_S(x))))) = p'^{n-1}(index_S(p(x))) = index_S(y), so p^{n-1}(p(x)) = y, i.e. p^n(x) = y.

**Lemma 10.D** p and p' have the same cycles; in particular:
(1) x = p^k(x) if and only if index_S(x) = p'^k(index_S(x))
(2) p(x), ..., p^k(x) are all distinct if and only if p'(index_S(x)), ..., p'^k(index_S(x)) are all distinct
**Proof.** (1) is a restatement of Lemma 10.C.  (2) follows from Lemma 10.C and the existence of inverse permutations (i.e. p^i(x) = p^j(x) and i < j implies x = p^{j-i}(x)).

**Lemma 10.14** The to-permutation and from-permutation for a rearrangement are inverses of each other.
**Proof.** Let t and f be the to and from permutations for a rearrangement r, and let i be an arbitrary iterator in the input  range of a particular call to r.  If t(i) = j, then j points to the destination of source(i) under the rearrangement r.  But then i points to the origin of source(j) under the rearrangement r, so f(j) = i.  Thus f o t(i) = i.  On the other hand, let j be an arbitrary iterator in the output range of a particular call to r.  If f(j) = i, then i points to the origin of source(j) under the rearrangement r.  But then j points to the destination of source(i) under the rearrangement r, so t(i) = j.  Thus t o f(j) = j, and we conclude that t and f are inverses.

**Lemma 10.15** Given a from-permutation, it is possible to perform a mutative rearrangement using n + c_N - c_T assignments, where n is the number of elements, c_N the number of nontrivial cycles, and c_T the number of trivial cycles.
**Proof.** We begin with the following observations:
  **Lemma 10.15.1** my_cycle_from performs no assignments if i is in a trivial cycle, and n + 1 assignments for a nontrivial cycle of size n.
  **Proof.** In the case of a trivial cycle, f(i) == i, so the procedure returns immediately.  Otherwise, the procedure performs one assignment (to initialize tmp), one assignment for each case k == f(i), k == f^2(i), ..., k == f^{n-1}(i).  Finally, the procedure performs one final assignment after the while loop for the case k == f^n(i), i.e. k == i, for a total of n + 1 assignments.
  **Lemma 10.15.2** cycle_representative returns true for exactly one element of any cycle.
  **Proof.** Suppose cycle_representative returns true for both i and j.  Then we would have both r(i, j) and r(j, i), so by the precondition that r is a total ordering, i and j must be the same element.

By Lemma 10.6, each element belongs to a unique cycle; thus the sum of the number of elements of each cycle of the permutation is the total size of the set being permuted.  By Lemma 10.15.1 and 10.15.2, my_rearrange_from performs (|C| + 1) assignments for each nontrivial cycle.  We split the sum over two parts (a sum over |C| and sum over 1).  For the first part, since the sum of the sizes of all the trivial cycles is simply the number of trivial cycles and the sum over all cycles is n (the total size of the set being permuted), the sum of the sizes of all the nontrivial cycles is n - c_T.  Finally, summing 1 over c_N different indices simply produces c_N, for a total of n + c_N - c_T assignments.

**Lemma 10.16** The number of nontrivial cycles in a reverse permutation is floor(n / 2); the number of trivial cycles is n mod 2.
**Proof.** By Lemma 10.D, it suffices to prove the lemma for the index permutation p(i) = (n - 1) - i.

Suppose n is even.  Then for any i in [0, n) we have p(i) = n - 1 - i; n - 1 is odd, so if i is even n - 1 - i is odd, and if i is odd then n - 1 - i is even.  It follows that p(i) != i.  Furthermore, p(p(i)) = p(n - 1 - i) = n - 1 - (n - 1 - i) = i, so every element belongs to a cycle of size 2, i.e. every cycle has size 2 (and there are no trivial cycles, i.e. n mod 2 = 0 trivial cycles).  By Lemma 10.6, each element belongs to a unique cycle; thus upon distributing the n elements among cycles of size 2, we find that there are exactly n / 2 (nontrivial) cycles.  Note that n / 2 = floor(n / 2) when n is even.

Next, suppose n is odd.  Suppose i < (n - 1) / 2; then p(i) = (n - 1) - i > (n - 1) - (n - 1) / 2 = (n - 1) / 2, so p(i) != i.  Similarly, if i > (n - 1) / 2, then p(i) = (n - 1) - i < (n - 1) - (n - 1) / 2 = (n - 1) / 2, so p(i) != i.  Furthermore, in both of these cases, p(p(i)) = (n - 1) - (n - 1 - i) = i, so every element that satisfies i < (n - 1) / 2 or i > (n - 1) / 2 belongs to a cycle of size 2.  However, if i = (n - 1) / 2, then p(i) = n - 1 - (n - 1) / 2 = (n - 1) / 2 = i, so in this case i belongs to a trivial cycle.  Thus there are (n - 1) / 2 = floor(n / 2) cycles of size 2, and one (i.e. n mod 2) trivial cycle.

**Lemma 10.17** floor(n / 2) is the largest possible number of nontrivial cycles in a permutation.
**Proof.** Suppose a permutation has k nontrivial cycles.  Each nontrivial cycle has at least 2 distinct elements, and by Lemma 10.6, each element belongs to at most one nontrivial cycle; thus among the k nontrivial cycles, there are 2k distinct elements.  If k > floor(n / 2) then we would have k >= (n + 1) / 2, but then there would be n + 1 distinct elements among the k nontrivial cycles, which is impossible.

**Lemma 10.19** The reverse permutation on [0, n) is the only permutation satisfying i < j => p(j) < p(i)
**Proof.** We will first show that the reverse permutation indeed satisfies this condition.  Suppose i < j; then -j < -i, so n - 1 - j < n - 1 - i.

Next, we will show that this condition uniquely determines the permutation.  Since 0 < 1 < ... < n - 1, repeated application of the condition gives p(n - 1) < p(n - 2) < ... < p(1) < p(0).
  **Lemma 10.19.1** If a_0 < ... < a_{n-1} are elements of [0, n), then a_i = i.
  **Proof.** We proceed by induction.  If n = 1, then the claim is trivial.  Suppose n > 1 and the claim holds for n - 1.  If a_{n-1} < n - 1, then we would either have a_i = a_j for some i != j, or a_i = n - 1 and a_{n-1} < a_i for some i < n - 1; both of these cases violate the condition a_0 < ... < a_{n-1}, so we must have a_{n-1} = n - 1; thus a_0 < ... < a_{n-2} are elements of [0, n - 1) and the claim follows by the inductive hypothesis.

By Lemma 10.19.1, it follows that p(n - 1) = 0, p(n - 2) = 1, and so on, i.e. p(i) = n - 1 - i.

**Lemma 10.E** The index permutation p corresponding to reverse_n_forward satisfies i < j => p(j) < p(i).
**Proof.** We will proceed by induction on n.  If n = 1, there is nothing to prove.

Suppose n > 1 and the claim holds for all m < n.

Let i < j, and define the following index permutations:
  Let p1 be the index permutation on [0, n) corresponding to the result of the first recursive call
  Let p2 be the index permutation on [0, n) corresponding to the result of the second recursive call
  Let p_s be the index permutation on [0, n) corresponding to the result of my_swap_ranges_n

Note that p = p_s o p2 o p1, and consider the following cases:

(1) Suppose i < j < h.  The inductive hypothesis implies that p1(j) < p1(i); also, p2(k) = k for 0 <= k < h, and p_s preserves ordering among elements in [0, h); thus we have p(j) < p(i).
(2) Suppose h + n_mod_2 <= i < j < n.  The inductive hypothesis implies that p2(j) < p2(i); also, p1(k) = k for h + n_mod_2 <= i < j < n, and p_s preserves ordering among elements in [h + n_mod_2, n); thus we have p(j) < p(i).
(3) Suppose i < h and h + n_mod_2 <= j; then p1(i) < h, p2(p1(i)) = p1(i), and p_s(p1(i)) >= h + n_mod_2.  Furthermore, p1(j) = j, p2(j) >= h + n_mod_2, and p_s(p2(j)) < h.  We conclude that p(j) < p(i).
(4) Suppose n is odd, i = h, and i < j.  Then p(i) = i; furthermore, p1(j) = j, p2(j) > h, and ps(p2(j)) < h, so the claim holds.
(5) Finally, suppose n is odd, i < h, and j = h.  Then p(j) = j = h; furthermore, p1(i) < h, p2(p1(i)) = p1(i), and ps(p1(i)) > h, so the claim holds.

**Lemma 10.F** Let p, q be permutations, and let p', q' be the corresponding index permutations.  Then p and q are inverses if and only if p' and q' are inverses.
**Proof.** Suppose p(q(x)) = x for each x in S.  Then given i in [0, n), we have p'(q'(i)) = p'(index_S(q(choose_S(i)))) = index_S(p(choose_S(index_S(q(choose_S(i)))))) = index_S(p(q(choose_S(i)))) = index_S(choose_S(i)) = i.

Conversely, suppose p'(q'(i)) = i for each i in [0, n).  Then given x in S, we have p(q(x)) = p(choose_S(q'(index_S(x)))) = choose_S(p'(index_S(choose_S(q'(index_S(x)))))) = choose_S(p'(q'(index_S(x)))) = choose_S(index_S(x)) = x.

**Lemma 10.21** The inverse of a k-rotation of n elements is an (n - k) rotation.
**Proof.** By Lemma 10.F, it suffices to show that the corresponding index index permutations p'(i) = (i + k) mod n and q'(i) = (i - k) mod n are inverses.  Let i be an arbitrary index in [0, n).  Then p'(i) is congruent to i + k (mod n), and p'(q'(i)) is congruent to i + k - k = i (mod n), and since i is the unique integer in [0, n) congruent to itself mod n, we conclude that p'(q'(i)) = i.  Similarly, p'(i) is congruent to i - k (mod n) and q'(p'(i)) is congruent to i - k + k = i (mod n), so q'(p'(i)) = i.

**Lemma 10.G** a / gcd(a, b) and b / gcd(a, b) are relatively prime.
**Proof.** Suppose d divides a / gcd(a, b) and divides b / gcd(a, b).  Then d * gcd(a, b) divides a and d * gcd(a, b) divides b, which would contradict the definition of gcd if |d| != 1.

**Lemma 10.H** lcm(a, b) * gcd(a, b) = a * b.
**Proof.** First note that a divides a * b / gcd(a, b) (since b / gcd(a, b) is an integer) and that b divides a * b / gcd(a, b); thus lcm(a, b) is at most a * b / gcd(a, b).

Next, write lcm(a, b) = k * b.  Then a divides k * b, i.e. a / gcd(a, b) divides k * b / gcd(a, b).  But a / gcd(a, b) and b / gcd(a, b) are relatively prime, so a / gcd(a, b) divides k, i.e. a / gcd(a, b) <= k.  So lcm(a, b) is at least a * b / gcd(a, b).  We conclude that lcm(a, b) = a * b / gcd(a, b).

**Lemma 10.I** k-rotation of a range [f, l) is equivalent to interchanging the relative positions of the values in the subranges [f, m) and [m, l), where m = f + ((l - f) - k) = l - k.
**Proof.** Interchanging the relative positions of the values in [f, m) and [m, l) has the following effect:

    (1) For any x in [f, m), the new value at x + (l - m) becomes the old value at x
    (2) For any x in [m, l), the new value at f + (x - m) becomes the old value at x

We will show that this is equivalent to a k-rotation.  Given an element x in [f, m), we have p(x) = x + k = x + (l - m); note that x precedes m, so x + (l - m) precedes m + (l - m) = l.  Next, given an element x in [m, l), we have p(x) = x + k - (l - f) = x + (l - m) - (l - f) = m + (x - m) + (l - m) - (l - f) = l + (x - m) - (l - f) = f + (x - m).  Note that we can rewrite x as x - m because either x = m or x precedes m.

**Lemma 10.22** Rotating a range [f, l) around the iterator m and then rotating it around the returned value m' returns m and restores the range to its original state.
**Proof.** Lemma 10.I shows that rotating a range around the iterator m is equivalent to a k-rotation, where k = l - m.  Furthermore, rotating a range around the iterator m returns the iterator m', where m' - f = k.  But then rotating around m' is equivalent to a j-rotation, where j = l - m' = l - (f + k) = (l - f) - k = n - k, i.e. an (n-k) rotation.  Since i + k + (n - k) = i (mod k) for any i, it follows that rotation around m and rotation around m' are inverse operations.

**Lemma 10.23** The k-rotation on [0, n) is the only permutation p that inverts the relative ordering between the subranges [0, n - k) and [n - k, n) but preserves the relative ordering within each subrange:

(1) i < n - k ^ n - k <= j < n => p(j) < p(i)
(2) i < j < n - k v n - k <= i < j => p(i) < p(j)

**Proof.** We will show that conditions (1) and (2) uniquely determine a permutation, and that the permutation is precisely a k-rotation.
  **Lemma 10.23.1** Suppose 0 <= m < k.  Then p(n - k + m) = m.
  **Proof.** We proceed by induction.  First consider the case m = 0.  If p(n - k) > 0, then condition (2) implies that p(i) = 0 is only possible when i < n - k.  But this would violate condition (1), so we conclude that p(n - k) = 0.  Now suppose m > 0.  If p(n - k + m) > m, then condition (2) implies that p(i) = m is only possible when i < n - k + m.  Since p(i) != m for i = n - k, n - k + 1, ..., n - k + (m - 1), we must have i < n - k.  But this would violate condition (1), so we conclude that p(n - k + m) = m.
  **Lemma 10.23.2** Suppose 0 <= m < n - k.  Then p(m) = m + k.
  **Proof.** By Lemma 10.23.1, p(0) cannot be 0, 1, ..., k - 1.  Suppose p(0) > k.  Then we would have p(i) < p(0) for some i in 1, 2, ..., n - k - 1, which contradicts (2).  Thus p(0) = k.  Next, by Lemma 10.23.1 and the inductive hypothesis, p(m) cannot be 0, 1, ..., m + k - 1.  Suppose p(m) > m + k.  Then we would have p(i) < p(m) for some m in m + 1, ..., n - k - 1, which contradicts (2).  Thus p(m) = m + k.

Together, Lemma 10.23.1 and 10.23.2 imply that p must be a k-rotation.

**Lemma 10.25** The first time the else clause is taken in rotate_forward_annotated, f = m', the standard return value for rotate.
**Proof.** We will proceed by induction on n, the number of times the procedure executed the while loop and took the if clause.

If n = 0, then the procedure takes the else clause immediately.  Let x0 be the element at f at the beginning of the procedure.  At the beginning of the else clause, the element at m is x0; the next iteration will set the element at f to x0, at which point x0 will be in its final position.

Suppose n > 0; we will show that if an iteration of the while loop takes the if clause, then the updated values of f, m, l would produce the same standard return value m' as the original values of f, m, l.

Given the original values f0, m0, l0, the standard return value m' is f0 + (l0 - m0).  In the case where the first element of the pair returned by my_swap_ranges_bounded is equal to m, the iteration sets f to m (i.e. we advance f by m - f), sets m to m + (m - f) (since my_swap_ranges_bounded advances both of its input ranges by the same amount), and leaves l unchanged.  But at the end of the iteration, we have f + (l - m) = f0 + (m0 - f0) + (l0 - (m0 + (m0 - f0))) = f0 + (m0 - f0) + (l0 - m0) - (m0 - f0) = f0 + (l0 - m0) = m'.

Thus the first iteration will result in updated values of f, m, l that produce the same standard return value m' as the original values of f, m, l.  By the inductive hypthesis, after the procedure executes n - 1 more iterations of the while loop taking the if clause and 1 iteration of the while loop taking the else clause, we will have f = m'.

**Lemma 10.26** The postcondition for rotate_partial_nontrivial is that it performs a partial rotation such that the objects in positions [m', l) are k-rotated where k = -(l - f) mod (m - f).
**Proof.** Consider the sequence of swaps made by the call to my_swap_ranges(m, l, f).
  **Lemma 10.26.1** After n calls to my_swap_step, the elements [f1, f0) are a -n-rotation of the original elements at [f, m).
  **Proof.** Since we call my_swap_ranges with f1 = f, f0 = l, the claim holds for n = 0 (the elements [f, m) are not rotated, i.e. they are a -0-rotation).  Suppose n > 0 and the claim holds for n - 1.  Then after n - 1 calls to my_swap_step, the elements at [f1, f0) are a -(n - 1) rotation.  The n-th call exchanges the elements at f1 and f0 and then advances both f1 and f0.  But this has the effect of moving the first element of the old range [f1, f0) to the last position of the new range [f1, f0) and shifting the remaining elements forward by one position; this is precisely a -1-rotation of [f1, f0), which, together with the -(n - 1)-rotation from the previous n - 1 calls to my_swap_step, constitutes a -n-rotation of the original elements at [f, m).

By Lemma 10.26.1, after the call to swap_ranges, the elements at [f + (l - m), l) = [m', l) are a -(l - m)-rotation of the original (m - f) elements at [f, m).  Lemma 10.26 follows from the fact that -(l - f) = -((l - m) + (m - f)) = -(l - m) mod (m - f).

**Lemma 11.1** If m = potential_partition_point(f, l, p) then count_if(f, m, p) = count_if_not(m, l, p).
**Proof.** m = potential_partition_point(f, l, p) means that after partitioning, the elements of [f, l) that do not satisfy p occupy [f, m); thus count_if_not(f, l, p) = m - f.  Thus count_if_not(f, l, p) = count_if_not(f, m, p) + count_if_not(m, l, p), and we can write:

    [1] count_if_not(f, m, p) + count_if_not(m, l, p) = m - f

Furthermore, before any partitioning has occurred, every element in [f, m) either satisfies or does not satisfy p.  Thus we can also write:

    [2] count_if(f, m, p) + count_if_not(f, m, p) = m - f

Combining [1] and [2] gives the desired result:

    [3] count_if(f, m, p) = count_if_not(m, l, p)

**Lemma 11.2** There are u!v! permutations that partition a range with u false values and v true values.
**Proof.** We will count the number of index permutations.  If u = 0 then any of the v! permutations of the all true input values is a valid partition.  Similarly, if v = 0 then any of the u! permutations of the all false input values is a valid partition.

Now consider the case where u > 0 and v > 0.  There are u choices of an index that maps to 0; for each of these u choices there are u - 1 choices of an index that maps to 1; and so on.  Furthermore, there are v choices of an index that maps to u; for each of these v choices there are v - 1 choices of an index that maps to u + 1; and so on.  This gives a total of u!v! choices.

Note that these are all the choices (for i = 0, 1, ..., u - 1 we must choose one of the u - i remaining positions with a false value, and likewise for i = u, u + 1, ..., u + v - 1 we must choose one of the u + v - i remaining positions with a true value).  Furthermore, we did not double count any choices (making a different choice at any step results in a different permutation).

**Lemma 11.3** The result of a stable partition is unique.
**Proof.** We will count the number of index permutations.  If there are no false values, then a stable partition must return its input (any other result would change the relative order between the all true values of the input).  Similarly, if there are no true values, then a stable partition must return its input.

Now consider the case where u > 0 and v > 0.  The index that maps to 0 must be the smallest index containing a false value, the index that maps to 1 must be the second smallest, and so forth.  Similarly, the index that maps to u must be the smallest index containing a true value, the index that maps to 1 must be the second smallest, and so forth.

At each step i there was exactly one possible choice for an index that maps to i (without violating stability), so we conclude that the permutation is uniquely determined.

**Lemma 11.A** partition_semistable does in fact partition its input.
**Proof.** We will first show that any point in the while loop, i is the first element of [f, l) that satisfies p, and that every element of [i, j) satisfies p.  Initially, this is true by the definition of find_if (and the fact that [i, successor(i)) only contains i).

Suppose the condition holds at the beginning of the loop.

The statement j = find_if_not(i, l, p) leaves i unchanged and sets j to the first element of [j, l) not satisfying p (or l if no such element exists); in particular, every element of [i, j) still satisfies p (this gives us Lemma 11.4).

After the exit test, we already know that p(source(i)) holds, and since j != l, we also know that !p(source(j)) holds (this gives us Lemma 11.5).

Finally, after the call of my_swap_step(i, j), the old element i no longer satisfies p, so the new element i (the successor of the old element i) is still the first element of [f, l) that satisfies p.  Furthermore, the old element j does satisfy p, so every element of [i, j) (the j in the range denotes the new element j, i.e. the successor of the old element j) still satisfies p (this gives us Lemma 11.6).

In particular, we have shown that at any point in the while loop, none(f, i, p) ^ all(i, j, p) holds; thus it holds when partition_semistable returns, at which point j == l so none(f, i, p) ^ all(i, l, p) holds, the range has been p-partitioned, and i is the partition point.

**Lemma 11.B** partition_semistable is in fact semistable.
**Proof.** The only statement that changes any elements is the call of swap_step.  The proof of Lemma 11.A shows that before this call, every element of [i, j) satisfies p; thus performing the swap does not affect the relative ordering of any elements not satisfying p.

**Lemma 11.7** A partition rearrangement that returns the partition point requres n applications of the predicate.
**Proof.** Upon applying fewer than n applications of the predicate, there is an element in the range for which the predicate has not been applied.  However, whether that element's value satisfies the predicate or not affects the partition point; thus a procedure that applies fewer than n applications of the predicate cannot return the correct partition point for every input range.

**Lemma 11.8** A partition rearrangement of a nonempty range that does not return the partition point requires n - 1 applications of the predicate.
**Proof.** If n = 1 then it suffices to return the input range without any applications of the predicate.  Suppose n >= 2 and some procedure applies the predicate fewer at most n - 2 times; then there are at least two elements i and j for which the predicate has not been applied.  If i does not satisfy the predicate and j does, then i must precede j in the output range, but if i satisfies the predicate and j does not, then j must precede i in the output range.  The procedure has no way of distinguishing between these two cases, and thus cannot return a correctly partitioned range in every case.

**Lemma 11.9** The number of times exchange_value is performed, v, equals the number of misplaced elements not satisfying the predicate.
**Proof.** If all or none of the elements satisfy the predicate, then the claim trivially holds, so we will only consider the case where v > 0.

By Lemma 11.1, the number of misplaced elements not satisfying the predicate is equal to the number of misplaced elements satisfying the predicate.  Since each iteration will swap one misplaced element satisfying the predicate and one misplaced element not satisfying the predicate, no elements will be misplaced after v iterations.

After v iterations, the next call to find_if(f, l, p) will return the partition point (if there were v misplaced elements in the original range that satisfy the predicate, then the v+1-st element in the original range that satisfies the predicate, counting forward is the partition point).  By similar reasoning (but counting backward rather than forward), the next call to find_backward_if_not(f, l, p) will also return the partition point (note that find_backward_if_not returns the successor of the element found), so f == l will hold, and the procedure will terminate.

**Lemma 11.10** combine_ranges is associative when applied to three nonoverlapping ranges.
**Proof.** First note that after rotating [f, l) around some m in [f, l], the range will consist of original elements in [m, l) followed by the original elements in [f, m), and the return value m' will be the new position of the original element at f.

Let x, y, z be pairs of iterators such that [x0, x1), [y0, y1), [z0, z1) are bounded ranges, and (x, y) as well as (y, z) satisfy the preconditions of combine_ranges.  Furthermore, let ++ denote concatenation of ranges.  Consider the statement combine_ranges(combine_ranges(x, y), z).  Initially, we have the following range:

    [x0, x1)++[x1, y0)++[y0, y1)++[y1, z0)++[z0, z1)

The inner call of combine_ranges will rotate [x0, y0) around x1, which will return the new position of x0 and result in the following:

    [x1, y0)++[x0, x1)++[y0, y1)++[y1, z0)++[z0, z1)

The outer call of combine ranges will rotate [x0, z0) around y1, which will return the new position of x0 and result in the following (1):

    [x1, y0)++[y1, z0)++[x0, x1)++[y0, y1)++[z0, z1)

Now consider the statement combine_ranges(x, combine_ranges(y, z)).  Initially, we have the following range:

    [x0, x1)++[x1, y0)++[y0, y1)++[y1, z0)++[z0, z1)

The inner call of combine_ranges will rotate [y0, z0) around y1, which will return the new position of y0 and result in the following:

    [x0, x1)++[x1, y0)++[y1, z0)++[y0, y1)++[z0, z1)

The outer call of combine ranges will rotate [x0, y0) around x1, which will return the new position of x0 and result in the following:

    [x1, y0)++[y1, z0)++[x0, x1)++[y0, y1)++[z0, z1)

This is identical to [1], so we conclude that combine_ranges is associative.

**Lemma 11.11** If for some predicate p,

    all(x0, x1, p) ^ none(x1, y0, p) ^ all(y0, y1, p)

then after z = combine_ranges(x, y), the following holds:

    none(x0, z0, p) ^ all(z0, z1, p)

**Proof.** Using the same notation as the proof of the previous lemma, initially we have the following range:

    [x0, x1) ++ [x1, y0) ++ [y0, y1)

Calling combine_ranges will rotate [x0, y0) around x1 and return the new position of x0:

    [x1, y0) ++ [x0, x1) ++ [y0, y1)

Thus z0 is the new position of x1 and z1 is the old position of y1, and the value at x0 is the old value at x1.  Since the values in the new range [x0, z0) are the values in the old range [x1, y0) and none(x1, y0, p) holds for the old range, it follows that none(x0, z0, p) holds for the new range.  Since the values in the new range [z0, z1) are the combined values of the two old ranges [x0, x1) and [y0, y1), and since all(x0, x1, p) and all(y0, y1, p) hold, it follows that all(z0, z1, p) holds for the new range.

**Lemma 11.14** The postcondition for sort_n_with_buffer is increasing_counted_range(f, n, r).
**Proof.** We proceed by induction on n.  If n = 0 or n = 1 then the claim trivially holds.  Suppose n > 1 and the claim holds for m < n.  By the inductive hypothesis the following conditions hold immediately before the call of merge_n_with_buffer:
    increasing_counted_range(f, h, r)
    increasing_counted_range(m, n - h, r)
Furthermore, the preconditions ensure that the following conditions also hold:
    mutable_counted_range(f, h + (n - h), r)
    weak_ordering(r)
    mutable_counted_range(f_b, h)
Thus the preconditions for merge_n_with_buffer are satisfied, and by Lemma 11.12, increasing_counted_range(f, h + (n - h), r) holds when sort_n_with_buffer returns.

**Lemma 11.15** sort_n_with_buffer is stable.
**Proof.** We again proceed by induction.  If n = 0 or n = 1 then there is nothing to prove.  If n > 1, stability follows by the inductive hypothesis and stability of merge_n_with_buffer (Lemma 11.13).

**Lemma 11.16** The rotate in merge_n_step_0 does not change the relative positions of elements with equivalent values.
**Proof.** Lemma 10.23 implies that the rotation preserves relative orderings between elements within the two separate subranges [f0_1, f1) and [f1, f1_0).

By definition of lower_bound_n, every element in [f1, f1_1) is strictly less than the element at source(f0_1).  Furthermore, the precondition mergeable(f0, n0, f1, n1, r) implies that every element in [f0_1, f1) is greater than or equal to the element at source(f0_1).  Thus before the rotation, every element in [f0_1, f1) is greater than every element in [f1, f1_0), so there are no equivalent values between the two subranges.

**Lemma 11.17** After merge_n_step_0, predecessor(f1_0) is a pivot.
**Proof.** Note the following:

    [f0, f1) is an increasing range, so every element in [f0_0, f0_1) has a value less than or equal to the value originally at f0_1
    [[f1, n1|) is an increasing range, so if f1_1 = lower_bound_n(f1, n1, r) then every element in [[f1_1, n1_1|) has a value greater than or equal to the value originally at f0_1
    [f0, f1) is an increasing range, so before the rotation, every element in [f0_1, f1) has a value greater than or equal to the value originally at f0_1
    [[f1, n1|) is an increasing range, so before the rotation, every element in [f1, f1_1) has a value strictly less than the value originally at f0_1
    After the rotation, the new value at f1_0 is the value originally at f0_1
    After the rotation, the new values in [f0_1, f1_0) are the old values in [f1, f1_1)
    After the rotation, the new values in [f1_0, f1_1) are the old values in [f0_1, f1)

Combining all of these results, it follows that the value at f1_0 immediately after the rotation is a pivot; since merge_n_step_0 sets f1_0 to its successor before returning, we conclude that after merge_n_step_0 returns, predecessor(f1_0) is a pivot.

**Lemma 11.18** merge_n_adaptive terminates with an increasing range.
**Proof.** This follows by induction and Lemma 11.17 (after the call to merge_n_step, predecessor(f1_0) is a pivot).

**Lemma 11.19** merge_n_adaptive is stable.
**Proof.** This follows by induction and Lemma 11.16 (note that the rotate is the only statement in merge_n_step that may rearrange values).

**Lemma 11.20** There are at most floor(lg(min(n0, n1))) + 1 recursive levels.
**Proof.** We will consider the case of an empty buffer (a non-empty buffer can only cause there to be fewer recursive levels).    If min(n0, n1) = n1, then after merge_n_step_1, both n0_1 and n1_1 will be at most n1 / 2.  Otherwise, after merge_n_step_0, both n0_0 and n1_0 will be at most n0 / 2.  Either way, the two recursive calls to merge_n_adaptive with new values n0', n1' satisfy min(n0', n1') < min(n0, n1) / 2.

Note that if either n0 = 1 or n1 = 1, then both recursive calls to merge_n_adaptive will return immediately, which establishes the base case (1 recursive level if min(n0, n1) = 1).  Otherwise, there is one more recursive level than the case of min(n0, n1) / 2, thus by the inductive hypothesis, 1 + floor(lg(min(n0, n1) / 2)) + 1 = 1 + floor(lg(min(n0, n1)) - 1) + 1 = floor(lg(min(n0, n1))) + 1.