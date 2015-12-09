#ifndef MY_SELECTION
#define MY_SELECTION

#include <cassert>
#include "my_intrinsics.h"
#include "my_type_functions.h"

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

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_2(const Domain(R)& a,
                            const Domain(R)& b,
                            R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return b;
    return a;
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_0_2(Domain(R)& a,
                      Domain(R)& b,
                      R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return b;
    return a;
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_2(const Domain(R)& a,
                            const Domain(R)& b,
                            R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return a;
    return b;
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_1_2(Domain(R)& a,
                      Domain(R)& b,
                      R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return a;
    return b;
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_3(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            R r)
{
    return select_0_2(select_0_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_0_3(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      R r)
{
    return select_0_2(select_0_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_3(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            R r)
{
    return select_1_2(select_1_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_2_3(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      R r)
{
    return select_1_2(select_1_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_3_ab(const Domain(R)& a,
                               const Domain(R)& b,
                               const Domain(R)& c,
                               R r)
{
    if (!r(c, b)) return b;
    return select_1_2(a, c, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_1_3_ab(Domain(R)& a,
                         Domain(R)& b,
                         Domain(R)& c,
                         R r)
{
    if (!r(c, b)) return b;
    return select_1_2(a, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_3(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            R r)
{
    if (r(b, a)) return select_1_3_ab(b, a, c, r);
    return              select_1_3_ab(a, b, c, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_1_3(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      R r)
{
    if (r(b, a)) return select_1_3_ab(b, a, c, r);
    return              select_1_3_ab(a, b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_4(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            const Domain(R)& d,
                            R r)
{
    return select_0_2(select_0_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_0_4(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      Domain(R)& d,
                      R r)
{
    return select_0_2(select_0_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_3_4(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            const Domain(R)& d,
                            R r)
{
    return select_1_2(select_2_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_3_4(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      Domain(R)& d,
                      R r)
{
    return select_1_2(select_2_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab_cd(const Domain(R)& a,
                                  const Domain(R)& b,
                                  const Domain(R)& c,
                                  const Domain(R)& d,
                                  R r)
{
    if (r(c, a)) return select_0_2(a, d, r);
    return              select_0_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_1_4_ab_cd(Domain(R)& a,
                            Domain(R)& b,
                            Domain(R)& c,
                            Domain(R)& d,
                            R r)
{
    if (r(c, a)) return select_0_2(a, d, r);
    return              select_0_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab(const Domain(R)& a,
                               const Domain(R)& b,
                               const Domain(R)& c,
                               const Domain(R)& d,
                               R r)
{
    if (r(d, c)) return select_1_4_ab_cd(a, b, d, c, r);
    return              select_1_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_1_4_ab(Domain(R)& a,
                         Domain(R)& b,
                         Domain(R)& c,
                         Domain(R)& d,
                         R r)
{
    if (r(d, c)) return select_1_4_ab_cd(a, b, d, c, r);
    return              select_1_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            const Domain(R)& d,
                            R r)
{
    if (r(b, a)) return select_1_4_ab(b, a, c, d, r);
    return              select_1_4_ab(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_1_4(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      Domain(R)& d,
                      R r)
{
    if (r(b, a)) return select_1_4_ab(b, a, c, d, r);
    return              select_1_4_ab(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4_ab_cd(const Domain(R)& a,
                                  const Domain(R)& b,
                                  const Domain(R)& c,
                                  const Domain(R)& d,
                                  R r)
{
    if (r(d, b)) return select_1_2(a, d, r);
    return              select_1_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_2_4_ab_cd(Domain(R)& a,
                            Domain(R)& b,
                            Domain(R)& c,
                            Domain(R)& d,
                            R r)
{
    if (r(d, b)) return select_1_2(a, d, r);
    return              select_1_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4_ab(const Domain(R)& a,
                               const Domain(R)& b,
                               const Domain(R)& c,
                               const Domain(R)& d,
                               R r)
{
    if (r(d, c)) return select_2_4_ab_cd(a, b, d, c, r);
    return              select_2_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_2_4_ab(Domain(R)& a,
                         Domain(R)& b,
                         Domain(R)& c,
                         Domain(R)& d,
                         R r)
{
    if (r(d, c)) return select_2_4_ab_cd(a, b, d, c, r);
    return              select_2_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4(const Domain(R)& a,
                            const Domain(R)& b,
                            const Domain(R)& c,
                            const Domain(R)& d,
                            R r)
{
    if (r(b, a)) return select_2_4_ab(b, a, c, d, r);
    return              select_2_4_ab(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
Domain(R)& select_2_4(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      Domain(R)& d,
                      R r)
{
    if (r(b, a)) return select_2_4_ab(b, a, c, d, r);
    return              select_2_4_ab(a, b, c, d, r);
}

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

template<int ia, int ib, typename R>
    requires(Relation(R))
Domain(R)& select_0_2(Domain(R)& a,
                      Domain(R)& b,
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
Domain(R)& select_1_4_ab_cd(Domain(R)& a,
                            Domain(R)& b,
                            Domain(R)& c,
                            Domain(R)& d,
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
Domain(R)& select_1_4_ab(Domain(R)& a,
                         Domain(R)& b,
                         Domain(R)& c,
                         Domain(R)& d,
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

template<int ia, int ib, int ic, int id, typename R>
    requires(Relation(R))
Domain(R)& select_1_4(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      Domain(R)& d,
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
Domain(R)& select_2_5_ab_cd(Domain(R)& a,
                            Domain(R)& b,
                            Domain(R)& c,
                            Domain(R)& d,
                            Domain(R)& e,
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
Domain(R)& select_2_5_ab(Domain(R)& a,
                         Domain(R)& b,
                         Domain(R)& c,
                         Domain(R)& d,
                         Domain(R)& e,
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

template<int ia, int ib, int ic, int id, int ie, typename R>
    requires(Relation(R))
Domain(R)& select_2_5(Domain(R)& a,
                      Domain(R)& b,
                      Domain(R)& c,
                      Domain(R)& d,
                      Domain(R)& e,
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
inline const Domain(R)& select_2_5(const Domain(R)& a,
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
inline Domain(R)& select_2_5(Domain(R)& a,
                             Domain(R)& b,
                             Domain(R)& c,
                             Domain(R)& d,
                             Domain(R)& e,
                             R r)
{
    return select_2_5<0, 1, 2, 3, 4>(a, b, c, d, e, r);
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
inline Domain(R)& median_5(Domain(R)& a,
                           Domain(R)& b,
                           Domain(R)& c,
                           Domain(R)& d,
                           Domain(R)& e,
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
Domain(R)& my_select_2_5_abc(Domain(R)& a,
                             Domain(R)& b,
                             Domain(R)& c,
                             Domain(R)& d,
                             Domain(R)& e,
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
Domain(R)& my_select_2_5_ab(Domain(R)& a,
                            Domain(R)& b,
                            Domain(R)& c,
                            Domain(R)& d,
                            Domain(R)& e,
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
Domain(R)& my_select_2_5(Domain(R)& a,
                         Domain(R)& b,
                         Domain(R)& c,
                         Domain(R)& d,
                         Domain(R)& e,
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

template<typename R>
    requires(Relation(R))
inline Domain(R)& my_median_5(Domain(R)& a,
                              Domain(R)& b,
                              Domain(R)& c,
                              Domain(R)& d,
                              Domain(R)& e,
                              R r)
{
    return my_select_2_5(a, b, c, d, e, r);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_0_2(const T& a,
                    const T& b)
{
    // Precondition:
    //     weak_ordering(r)
    if (b < a) return b;
    return a;
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_0_2(T& a,
              T& b)
{
    // Precondition:
    //     weak_ordering(r)
    if (b < a) return b;
    return a;
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_1_2(const T& a,
                    const T& b)
{
    // Precondition:
    //     weak_ordering(r)
    if (b < a) return a;
    return b;
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_1_2(T& a,
              T& b)
{
    // Precondition:
    //     weak_ordering(r)
    if (b < a) return a;
    return b;
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_0_3(const T& a,
                    const T& b,
                    const T& c)
{
    return select_0_2(select_0_2(a, b), c);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_0_3(T& a,
              T& b,
              T& c)
{
    return select_0_2(select_0_2(a, b), c);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_2_3(const T& a,
                    const T& b,
                    const T& c)
{
    return select_1_2(select_1_2(a, b), c);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_2_3(T& a,
              T& b,
              T& c)
{
    return select_1_2(select_1_2(a, b), c);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_1_3_ab(const T& a,
                       const T& b,
                       const T& c)
{
    if (!(c < b)) return b;
    return select_1_2(a, c);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_1_3_ab(T& a,
                 T& b,
                 T& c)
{
    if (!(c < b)) return b;
    return select_1_2(a, c);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_1_3(const T& a,
                    const T& b,
                    const T& c)
{
    if (b < a) return select_1_3_ab(b, a, c);
    return            select_1_3_ab(a, b, c);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_1_3(T& a,
              T& b,
              T& c)
{
    if (b < a) return select_1_3_ab(b, a, c);
    return            select_1_3_ab(a, b, c);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_0_4(const T& a,
                    const T& b,
                    const T& c,
                    const T& d)
{
    return select_0_2(select_0_3(a, b, c), d);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_0_4(T& a,
              T& b,
              T& c,
              T& d)
{
    return select_0_2(select_0_3(a, b, c), d);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_3_4(const T& a,
                    const T& b,
                    const T& c,
                    const T& d)
{
    return select_1_2(select_2_3(a, b, c), d);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_3_4(T& a,
              T& b,
              T& c,
              T& d)
{
    return select_1_2(select_2_3(a, b, c), d);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_1_4_ab_cd(const T& a,
                          const T& b,
                          const T& c,
                          const T& d)
{
    if (c < a) return select_0_2(a, d);
    return            select_0_2(b, c);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_1_4_ab_cd(T& a,
                    T& b,
                    T& c,
                    T& d)
{
    if (c < a) return select_0_2(a, d);
    return            select_0_2(b, c);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_1_4_ab(const T& a,
                       const T& b,
                       const T& c,
                       const T& d)
{
    if (d < c) return select_1_4_ab_cd(a, b, d, c);
    return            select_1_4_ab_cd(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_1_4_ab(T& a,
                 T& b,
                 T& c,
                 T& d)
{
    if (d < c) return select_1_4_ab_cd(a, b, d, c);
    return            select_1_4_ab_cd(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_1_4(const T& a,
                    const T& b,
                    const T& c,
                    const T& d)
{
    if (b < a) return select_1_4_ab(b, a, c, d);
    return            select_1_4_ab(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_1_4(T& a,
              T& b,
              T& c,
              T& d)
{
    if (b < a) return select_1_4_ab(b, a, c, d);
    return            select_1_4_ab(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_2_4_ab_cd(const T& a,
                          const T& b,
                          const T& c,
                          const T& d)
{
    if (d < b) return select_1_2(a, d);
    return            select_1_2(b, c);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_2_4_ab_cd(T& a,
                    T& b,
                    T& c,
                    T& d)
{
    if (d < b) return select_1_2(a, d);
    return            select_1_2(b, c);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_2_4_ab(const T& a,
                       const T& b,
                       const T& c,
                       const T& d)
{
    if (d < c) return select_2_4_ab_cd(a, b, d, c);
    return            select_2_4_ab_cd(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_2_4_ab(T& a,
                 T& b,
                 T& c,
                 T& d)
{
    if (d < c) return select_2_4_ab_cd(a, b, d, c);
    return            select_2_4_ab_cd(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& select_2_4(const T& a,
                    const T& b,
                    const T& c,
                    const T& d)
{
    if (b < a) return select_2_4_ab(b, a, c, d);
    return            select_2_4_ab(a, b, c, d);
}

template<typename T>
    requires(TotallyOrdered(T))
T& select_2_4(T& a,
              T& b,
              T& c,
              T& d)
{
    if (b < a) return select_2_4_ab(b, a, c, d);
    return            select_2_4_ab(a, b, c, d);
}

template<typename T>
bool stable_cmp(T x, T y, int ix, int iy)
{
    assert(ix != iy);
    if (ix < iy) return x < y;
    return !(y < x);
}

template<int ia, int ib, typename T>
    requires(TotallyOrdered(T))
const T& select_0_2(const T& a,
                    const T& b)
{
    if (stable_cmp(b, a, ib, ia)) return b;
    return a;
}

template<int ia, int ib, typename T>
    requires(TotallyOrdered(T))
T& select_0_2(T& a,
              T& b)
{
    if (stable_cmp(b, a, ib, ia)) return b;
    return a;
}

template<int ia, int ib, int ic, int id, typename T>
    requires(TotallyOrdered(T))
const T& select_1_4_ab_cd(const T& a,
                          const T& b,
                                  const T& c,
                                  const T& d)
{
    if (stable_cmp(c, a, ic, ia)) return
        select_0_2<ia,id,T>(a, d);
    return
        select_0_2<ib,ic,T>(b, c);
}

template<int ia, int ib, int ic, int id, typename T>
    requires(TotallyOrdered(T))
T& select_1_4_ab_cd(T& a,
                    T& b,
                    T& c,
                    T& d)
{
    if (stable_cmp(c, a, ic, ia)) return
        select_0_2<ia,id,T>(a, d);
    return
        select_0_2<ib,ic,T>(b, c);
}

template<int ia, int ib, int ic, int id, typename T>
    requires(TotallyOrdered(T))
const T& select_1_4_ab(const T& a,
                       const T& b,
                       const T& c,
                       const T& d)
{
    if (stable_cmp(d, c, id, ic)) return
        select_1_4_ab_cd<ia,ib,id,ic,T>(a, b, d, c);
    return
        select_1_4_ab_cd<ia,ib,ic,id,T>(a, b, c, d);
}

template<int ia, int ib, int ic, int id, typename T>
    requires(TotallyOrdered(T))
T& select_1_4_ab(T& a,
                 T& b,
                 T& c,
                 T& d)
{
    if (stable_cmp(d, c, id, ic)) return
        select_1_4_ab_cd<ia,ib,id,ic,T>(a, b, d, c);
    return
        select_1_4_ab_cd<ia,ib,ic,id,T>(a, b, c, d);
}

template<int ia, int ib, int ic, int id, typename T>
    requires(TotallyOrdered(T))
const T& select_1_4(const T& a,
                    const T& b,
                    const T& c,
                    const T& d)
{
    if (stable_cmp(b, a, ib, ia)) return
        select_1_4_ab<ib,ia,ic,id,T>(b, a, c, d);
    return
        select_1_4_ab<ia,ib,ic,id,T>(a, b, c, d);
}

template<int ia, int ib, int ic, int id, typename T>
    requires(TotallyOrdered(T))
T& select_1_4(T& a,
              T& b,
              T& c,
              T& d)
{
    if (stable_cmp(b, a, ib, ia)) return
        select_1_4_ab<ib,ia,ic,id,T>(b, a, c, d);
    return
        select_1_4_ab<ia,ib,ic,id,T>(a, b, c, d);
}

template<int ia, int ib, int ic, int id, int ie, typename T>
    requires(TotallyOrdered(T))
const T& select_2_5_ab_cd(const T& a,
                          const T& b,
                          const T& c,
                          const T& d,
                          const T& e)
{
    if (stable_cmp(c, a, ic, ia)) return
        select_1_4_ab<ia, ib, id, ie, T>(a, b, d, e);
    return
        select_1_4_ab<ic, id, ib, ie, T>(c, d, b, e);
}

template<int ia, int ib, int ic, int id, int ie, typename T>
    requires(TotallyOrdered(T))
T& select_2_5_ab_cd(T& a,
                    T& b,
                    T& c,
                    T& d,
                    T& e)
{
    if (stable_cmp(c, a, ic, ia)) return
        select_1_4_ab<ia, ib, id, ie, T>(a, b, d, e);
    return
        select_1_4_ab<ic, id, ib, ie, T>(c, d, b, e);
}

template<int ia, int ib, int ic, int id, int ie, typename T>
    requires(TotallyOrdered(T))
const T& select_2_5_ab(const T& a,
                       const T& b,
                       const T& c,
                       const T& d,
                       const T& e)
{
    if (stable_cmp(d, c, id, ic)) return
        select_2_5_ab_cd<ia, ib, id, ic, ie, T>(a, b, d, c, e);
    return
        select_2_5_ab_cd<ia, ib, ic, id, ie, T>(a, b, c, d, e);
}

template<int ia, int ib, int ic, int id, int ie, typename T>
    requires(TotallyOrdered(T))
T& select_2_5_ab(T& a,
                 T& b,
                 T& c,
                 T& d,
                 T& e)
{
    if (stable_cmp(d, c, id, ic)) return
        select_2_5_ab_cd<ia, ib, id, ic, ie, T>(a, b, d, c, e);
    return
        select_2_5_ab_cd<ia, ib, ic, id, ie, T>(a, b, c, d, e);
}

template<int ia, int ib, int ic, int id, int ie, typename T>
    requires(TotallyOrdered(T))
const T& select_2_5(const T& a,
                    const T& b,
                    const T& c,
                    const T& d,
                    const T& e)
{
    if (stable_cmp(b, a, ib, ia)) return
        select_2_5_ab<ib, ia, id, ic, ie, T>(b, a, d, c, e);
    return
        select_2_5_ab<ia, ib, ic, id, ie, T>(a, b, c, d, e);
}

template<int ia, int ib, int ic, int id, int ie, typename T>
    requires(TotallyOrdered(T))
T& select_2_5(T& a,
              T& b,
              T& c,
              T& d,
              T& e)
{
    if (stable_cmp(b, a, ib, ia)) return
        select_2_5_ab<ib, ia, id, ic, ie, T>(b, a, d, c, e);
    return
        select_2_5_ab<ia, ib, ic, id, ie, T>(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
inline const T& select_2_5(const T& a,
                           const T& b,
                           const T& c,
                           const T& d,
                           const T& e)
{
    return select_2_5<0, 1, 2, 3, 4>(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
inline T& select_2_5(T& a,
                     T& b,
                     T& c,
                     T& d,
                     T& e)
{
    return select_2_5<0, 1, 2, 3, 4>(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
inline const T& median_5(const T& a,
                         const T& b,
                         const T& c,
                         const T& d,
                         const T& e)
{
    return select_2_5<0, 1, 2, 3, 4>(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
inline T& median_5(T& a,
                   T& b,
                   T& c,
                   T& d,
                   T& e)
{
    return select_2_5<0, 1, 2, 3, 4>(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& my_select_2_5_abc(const T& a,
                           const T& b,
                           const T& c,
                           const T& d,
                           const T& e)
{
    if (d < b) {
        if (e < b) return
            select_2_3(a, d, e);
        return
            b;
    } else {
        if (e < b) return
            b;
        return
            select_0_3(c, d, e);
    }
}

template<typename T>
    requires(TotallyOrdered(T))
T& my_select_2_5_abc(T& a,
                     T& b,
                     T& c,
                     T& d,
                     T& e)
{
    if (d < b) {
        if (e < b) return
            select_2_3(a, d, e);
        return
            b;
    } else {
        if (e < b) return
            b;
        return
            select_0_3(c, d, e);
    }
}

template<typename T>
    requires(TotallyOrdered(T))
const T& my_select_2_5_ab(const T& a,
                          const T& b,
                          const T& c,
                          const T& d,
                          const T& e)
{
    if (c < b) {
        if (c < a) return
            my_select_2_5_abc(c, a, b, d, e);
        return
            my_select_2_5_abc(a, c, b, d, e);
    }
    return
        my_select_2_5_abc(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
T& my_select_2_5_ab(T& a,
                    T& b,
                    T& c,
                    T& d,
                    T& e)
{
    if (c < b) {
        if (c < a) return
            my_select_2_5_abc(c, a, b, d, e);
        return
            my_select_2_5_abc(a, c, b, d, e);
    }
    return
        my_select_2_5_abc(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
const T& my_select_2_5(const T& a,
                       const T& b,
                       const T& c,
                       const T& d,
                       const T& e)
{
    if (b < a) return
        my_select_2_5_ab(b, a, c, d, e);
    return
        my_select_2_5_ab(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
T& my_select_2_5(T& a,
                 T& b,
                 T& c,
                 T& d,
                 T& e)
{
    if (b < a) return
        my_select_2_5_ab(b, a, c, d, e);
    return
        my_select_2_5_ab(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
inline const T& my_median_5(const T& a,
                            const T& b,
                            const T& c,
                            const T& d,
                            const T& e)
{
    return my_select_2_5(a, b, c, d, e);
}

template<typename T>
    requires(TotallyOrdered(T))
inline T& my_median_5(T& a,
                      T& b,
                      T& c,
                      T& d,
                      T& e)
{
    return my_select_2_5(a, b, c, d, e);
}

#endif
