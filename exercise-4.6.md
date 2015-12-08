**Exercise 4.6** Prove the stability of every order-selection procedure in this section.

To show that an order-selection procedure select_i_j(a, b, ..., r) is stable, we need to show that if the procedure returns x, then precisely i elements y != x among a, b, ... satisfy r'((y, iy), (x, ix)).

select_0_2:

    select_0_2 returns a when r(b, a) does not hold; since the procedure (which is not templatized on stability indices) assumes that ia < ib, !r(b, a) implies r'((a, ia), (b, ib)), and trichotomy of the total order r' implies that r'((b, ib), (a, ia)) does not hold.

    select_0_2 returns b when r(b, a) holds; in this case, we must have r'((b, ib), (a, ia)), and trichotomy of r' implies that r'((a, ia), (b, ib)) does not hold.

select_1_2:

    If select_0_2 returns a, we need to show that r'((b, ib), (a, ia)) holds.  But select_0_2 only returns a when r(b, a) holds, and r(b, a) implies r'((b, ib), (a, ia)).  On the other hand, if select_0_2 returns b, then !r(b, a), and since select_1_2 implicitly assumes that ia < ib, it follows that r'((a, ia), (b, ib)) holds.

select_0_3:

    If select_0_2 returns a, then the inner call to select_0_2(a, b, r) must have returned a, which shows that r'((a, ia), (b, ib)) holds and r'((b, ib), (a, ia)) does not hold; furthermore, the outer call to select_0_2(a, c, r) must have returned a, which shows that r'((a, ia), (c, ic)) holds and r'((c, ic), (a, ia)) does not hold.

    If select_0_2 returns b, then the inner call to select_0_2(a, b, r) must have returned b, which shows that r'((b, ib), (a, ia)) holds and r'((a, ia), (b, ib)) does not hold; furthermore, the outer call to select_0_2(b, c, r) must have returned b, which shows that r'((b, ib), (c, ic)) holds and r'((c, ic), (b, ib)) does not hold.

    Finally, if select_0_2 returns c, then the outer call must have returned c, and transitivity of r' togther with the return value of the inner call shows that both r'((c, ic), (b, ib)) and r'((c, ic), (a, ia)) hold.

select_1_3_ab:

    This procedure assumes that r'((a, ia), (b, ib)) holds for its inputs a and b, and that ia < ic, ib < ic.  If !r(c, b), then we must have r'((b, ib), (c, ic)); thus a is the only element y for which r'((y, iy), (b, ib)) holds, and the procedure correctly returns b.  Otherwise, we have both r'((a, ia), (b, ib)) and r'((c, ic), (b, ib)), and stability of select_1_3_ab reduces to stability of select_1_2 (which we have already proved).

select_1_3:

    This procedure assumes that ia < ib < ic.  We have already shown that select_1_3_ab is stable for inputs a', b', c' if r'((a', ia'), (b', ib')) and ia' < ic', ib' < ic'.  If r(b, a), then r'((b, ib), (a, ia)) holds, and transitivity of < implies that ia < ic; thus taking ia' = ib, ib' = ia, ic' = ic shows that select_1_3 is stable in the case r(b, a).  Otherwise, r'((a, ia), (b, ib)) holds, and again transitivity of < implies that ia < ic; thus taking ia' = ia, ib' = ib, ic' = ic shows that select_1_3 is stable in the case !r(b, a).

select_2_3:

    This case is analogous to select_0_3.

select_1_4_ab_cd:

    This procedure assumes that:

        ia < ic
        ia < id
        ib < ic
        ib < id
        r'((a, ia), (b, ib))
        r'((c, ic), (d, id))

    If r(c, a) holds, so does r'((c, ic), (a, ia)), and transitivity of r' implies r'((c, ic), (b, ib)).  Furthermore, if select_0_2(a, d, r) returns a, then r'((a, ia), (d, id)) holds; thus c is the only element for which r'((c, ic), (a, ia)) holds, and the procedure correctly returns a.  Alternatively, if select_0_2(a, d, r) returns d, then r'((d, id), (a, ia)) holds; thus c is the only element for which r'((c, ic), (d, id)) holds, and the procedure correctly returns d.

    Otherwise, if r(c, a) does not hold, then r'((a, ia), (c, ic)) holds, and transitivity of r' implies r'((a, ia), (d, id)).  By similar reasoning as above, the return value of select_0_2(b, c, r) is the correct return value for select_1_4_ab_cd.

select_1_4_ab:

    This procedure assumes that:

        ia < ic
        ia < id
        ib < ic
        ib < id
        ic < id
        r'((a, ia), (b, ib))

    If r(d, c) holds then r'((d, id), (c, ic)) holds, and stability of select_1_4_ab reduces to stability of select_1_4_ab_cd with arguments a, b, d, c, r.  Similarly, if r(d, c) does not hold, then r'((c, ic), (d, id)) holds, and stability of select_1_4_ab reduces to stability of select_1_4_ab_cd with arguments a, b, c, d, r.

select_1_4:

    This procedure assumes that ia < ib < ic < id.  If r(b, a) holds then r'((b, ib), (a, ia)) holds, and stability of select_1_4 reduces to stability of select_1_4_ab with arguments b, a, c, d, r.  Similarly, if r(b, a) does not hold, then r'((a, ia), (b, ib)) holds, and stability of select_1_4 reduces to stability of select_1_4_ab with arguments a, b, c, d, r.

select_0_2 (templatized stability indices):

    First consider the case where ia < ib.  In this case, if cmp(b, a, r) returns true, then r(b, a) holds; thus r'((b, ib), (a, ia)) holds, i.e. r'((a, ia), (b, ib)) does not hold, and the procedure correctly returns b.  Otherwise, if cmp(b, a, r) returns false, then r(b, a) does not hold; thus r'((a, ia), (b, ib)) holds, i.e. r'((b, ib), (a, ia)) does not hold, and the procedure correctly returns a.

    Next, consider the case where !(ia < ib).  Note that we only use distinct stability indices, so we can assume that ib < ia in this case.  Then if cmp(b, a, r) returns true, !r(a, b) holds, r'((b, ib), (a, ia)) also holds, and r'((a, ia), (b, ib)) does not hold, and the procedure correctly returns b.  Finally, if cmp(b, a, r) returns false, then !r(a, b) does not hold, i.e. r(a, b) holds, r'((a, ia), (b, ib)) also holds, r'((b, ib), (a, ia)) does not hold, and the procedure correctly returns a.

select_1_4_ab_cd (templatized stability indices):

    This procedure assumes that:

        r'((a, ia), (b, ib))
        r'((c, ic), (d, id))

    First, consider the case where ia < ic.  If cmp(c, a, r) returns true, then r(c, a) holds, i.e. r'((c, ic), (a, ia)) holds, and by transitivity of r', r'((c, ic), (b, ib)) holds.

    If select_0_2<ia,id>(a, d, r) returns a, then we know that r'((a, ia), (d, id)) holds; thus r'((d, id), (a, ia)) does not hold, c is the only element for which r'((c, ic), (a, ia)) holds, and the procedure correctly returns a.  Similarly, if select_0_2<ia,id>(a, d, r) returns d, then c is the only element for which r'((c, ic), (d, id)) holds, and the procedure correctly returns d.

    Alternatively, if cmp(c, a, r) returns false, then r(c, a) does not hold, i.e. r'((a, ia), (c, ic)) holds, and by transitivity of r', r'((a, ia), (d, id)) holds.  By a similar argument to above, the subsequent call to select_0_2<ib,ic> will be the correct return value for the entire procedure.

    The case ic < ia is analogous, and we do not need to consider the case ia = ic (since the procedure implicitly assumes distinct stability indices).

select_1_4_ab (templatized stability indices):

    This procedure assumes that:

        r'((a, ia), (b, ib))

    The call to cmp(d, c, r) before the call to select_1_4_ab_cd ensures that the assumptions of select_1_4_ab_cd are satisfied; thus stability of select_1_4_ab reduces to stability of select_1_4_ab_cd.

select_1_4 (templatized stability indices):

    The call to cmp(b, a, r) before the call to select_1_4_ab ensures thta the assumptions of select_1_4_ab are satisfied; thus stability of select_1_4 reduces to stability of select_1_4_ab.

select_2_5_ab_cd (templatized stability indices):

    This procedure assumes that:

        r'((a, ia), (b, ib))
        r'((c, ic), (d, id))

    If cmp(c, a, r) returns true, then r'((c, ic), (a, ia)) holds.  In the subsequent call select_1_4_ab<ia,ib,ic,id>(a, b, d, e, r), the assumptions to select_1_4_ab are satisfied; thus there is exactly one element x among a, b, d, e, distinct from the return value y of the call to select_1_4_ab, such that r'((x, ix), (y, iy)).  If y is one of a, b, d, then we already know that r'((c, ic), (y, iy)), so there are exactly two elements z != y among a, b, c, d, e such that r'((z, iz), (y, iy)).  If y = e, then x is one of a, b, d, and transitivity of r' implies r'((c, ic), (e, ie)), and again there are exactly two elements z != y among a, b, c, d, e such that r'((z, iz), (y, iy)).  The case where cmp(c, a, r) returns false is analogous.

select_2_5_ab (templatized stability indices):

    This procedure assumes that:

        r'((a, ia), (b, ib))

    The call to cmp(d, c, r) before the call to select_2_5_ab_cd<...> ensures that the assumptions of select_2_5_ab_cd are satisfied; thus stability of select_2_5_ab reduces to stability of select_2_5_ab_cd.

select_2_5 (templatized stability indices):

    The call to cmp(b, a, r) before the call to select_2_5_ab<...> ensures that the assumptions of select_2_5_ab are satisfied; thus stability of select_2_5 reduces to stability of select_2_5_ab.
