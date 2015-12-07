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


