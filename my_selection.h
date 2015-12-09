#ifndef MY_SELECTION
#define MY_SELECTION

#include "my_intrinsics.h"
#include "my_type_functions.h"

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_2(const Domain(R) &a,
                            const Domain(R) &b,
                            R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return b;
    return a;
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_2(const Domain(R) &a,
                            const Domain(R) &b,
                            R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return a;
    return b;
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_3(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            R r)
{
    return select_0_2(select_0_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_3(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            R r)
{
    return select_1_2(select_1_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_3_ab(const Domain(R) &a,
                               const Domain(R) &b,
                               const Domain(R) &c,
                               R r)
{
    if (!r(c, b)) return b;
    return select_1_2(a, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_3(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            R r)
{
    if (r(b, a)) return select_1_3_ab(b, a, c, r);
    return              select_1_3_ab(a, b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    return select_0_2(select_0_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_3_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    return select_1_2(select_2_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab_cd(const Domain(R) &a,
                                  const Domain(R) &b,
                                  const Domain(R) &c,
                                  const Domain(R) &d,
                                  R r)
{
    if (r(c, a)) return select_0_2(a, d, r);
    return              select_0_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab(const Domain(R) &a,
                               const Domain(R) &b,
                               const Domain(R) &c,
                               const Domain(R) &d,
                               R r)
{
    if (r(d, c)) return select_1_4_ab_cd(a, b, d, c, r);
    return              select_1_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    if (r(b, a)) return select_1_4_ab(b, a, c, d ,r);
    return              select_1_4_ab(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4_ab_cd(const Domain(R) &a,
                                  const Domain(R) &b,
                                  const Domain(R) &c,
                                  const Domain(R) &d,
                                  R r)
{
    if (r(d, b)) return select_1_2(a, d, r);
    return              select_1_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4_ab(const Domain(R) &a,
                               const Domain(R) &b,
                               const Domain(R) &c,
                               const Domain(R) &d,
                               R r)
{
    if (r(d, c)) return select_2_4_ab_cd(a, b, d, c, r);
    return              select_2_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    if (r(b, a)) return select_2_4_ab(b, a, c, d, r);
    return              select_2_4_ab(a, b, c, d, r);
}

template<bool strict, typename R>
    requires(Relation(R))
struct compare_strict_or_reflexive;

template<typename R>
    requires(Relation(R))
struct compare_strict_or_reflexive<true, R>
{
    bool operator()(const Domain(R)& a,
                    const Domain(R)& b,
                    R r)
    {
        return r(a, b);
    }
};

template<typename R>
    requires(Relation(R))
struct compare_strict_or_reflexive<false, R>
{
    bool operator()(const Domain(R)& a,
                    const Domain(R)& b,
                    R r)
    {
        // complement_of_converse_r(a, b)
        return !r(b, a);
    }
};

template<int ia, int ib, typename R>
    requires(Relation(R))
const Domain(R)& select_0_2(const Domain(R)& a,
                            const Domain(R)& b,
                            R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return b;
    return a;
}

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab_cd(const Domain(R)& a,
                                  const Domain(R)& b,
                                  const Domain(R)& c,
                                  const Domain(R)& d,
                                  R r)
{
    compare_strict_or_reflexive<(ia < ic), R> cmp;
    if (cmp(c, a, r)) return
        select_0_2<ia,id,R>(a, d, r);
    return
        select_0_2<ib,ic,R>(b, c, r);
}

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab(const Domain(R)& a,
                               const Domain(R)& b,
                               const Domain(R)& c,
                               const Domain(R)& d,
                               R r)
{
    compare_strict_or_reflexive<(ic < id), R> cmp;
    if (cmp(d, c, r)) return
        select_1_4_ab_cd<ia,ib,id,ic,R>(a, b, d, c, r);
    return
        select_1_4_ab_cd<ia,ib,ic,id,R>(a, b, c, d, r);
}

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
const Domain(R)& select_1_4(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            const Domain(R)& d,
                            R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return
        select_1_4_ab<ib,ia,ic,id,R>(b, a, c, d, r);
    return
        select_1_4_ab<ia,ib,ic,id,R>(a, b, c, d, r);
}

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
const Domain(R)& select_2_5_ab_cd(const Domain(R)& a,
                                  const Domain(R)& b,
                                  const Domain(R)& c,
                                  const Domain(R)& d,
                                  const Domain(R)& e,
                                  R r)
{
    compare_strict_or_reflexive<(ia < ic), R> cmp;
    if (cmp(c, a, r)) return
        select_1_4_ab<ia, ib, id, ie, R>(a, b, d, e, r);
    return
        select_1_4_ab<ic, id, ib, ie, R>(c, d, b, e, r);
}

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
const Domain(R)& select_2_5_ab(const Domain(R)& a,
                               const Domain(R)& b,
                               const Domain(R)& c,
                               const Domain(R)& d,
                               const Domain(R)& e,
                               R r)
{
    compare_strict_or_reflexive<(ic < id), R> cmp;
    if (cmp(d, c, r)) return
        select_2_5_ab_cd<ia, ib, id, ic, ie, R>(a, b, d, c, e, r);
    return
        select_2_5_ab_cd<ia, ib, ic, id, ie, R>(a, b, c, d, e, r);
}

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
const Domain(R)& select_2_5(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            const Domain(R)& d,
                            const Domain(R)& e,
                            R r)
{
    compare_strict_or_reflexive<(ia < ib), R> cmp;
    if (cmp(b, a, r)) return
        select_2_5_ab<ib, ia, id, ic, ie, R>(b, a, d, c, e, r);
    return
        select_2_5_ab<ia, ib, ic, id, ie, R>(a, b, c, d, e, r);
}

template<typename R>
    requires(Relation(R))
inline const Domain(R)& median_5(const Domain(R)& a,
                                 const Domain(R)& b,
                                 const Domain(R)& c,
                                 const Domain(R)& d,
                                 const Domain(R)& e,
                                 R r)
{
    return select_2_5<0, 1, 2, 3, 4>(a, b, c, d, e, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& my_select_2_5_abc(const Domain(R)& a,
                                   const Domain(R)& b,
                                   const Domain(R)& c,
                                   const Domain(R)& d,
                                   const Domain(R)& e,
                                   R r)
{
    if (r(d, b)) {
        if (r(e, b)) return
            select_2_3(a, d, e, r);
        return
            b;
    } else {
        if (r(e, b)) return
            b;
        return
            select_0_3(c, d, e, r);
    }
}

template<typename R>
    requires(Relation(R))
const Domain(R)& my_select_2_5_ab(const Domain(R)& a,
                                  const Domain(R)& b,
                                  const Domain(R)& c,
                                  const Domain(R)& d,
                                  const Domain(R)& e,
                                  R r)
{
    if (r(c, b)) {
        if (r(c, a)) return
            my_select_2_5_abc(c, a, b, d, e, r);
        return
            my_select_2_5_abc(a, c, b, d, e, r);
    }
    return
        my_select_2_5_abc(a, b, c, d, e, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& my_select_2_5(const Domain(R)& a,
                               const Domain(R)& b,
                               const Domain(R)& c,
                               const Domain(R)& d,
                               const Domain(R)& e,
                               R r)
{
    if (r(b, a)) return
        my_select_2_5_ab(b, a, c, d, e, r);
    return
        my_select_2_5_ab(a, b, c, d, e, r);
}

template<typename R>
    requires(Relation(R))
inline const Domain(R)& my_median_5(const Domain(R)& a,
                                    const Domain(R)& b,
                                    const Domain(R)& c,
                                    const Domain(R)& d,
                                    const Domain(R)& e,
                                    R r)
{
    return my_select_2_5(a, b, c, d, e, r);
}

#endif
