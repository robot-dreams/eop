#include <iostream>
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename I>
    requires(Iterator(I))
void increment(I& x)
{
    // Precondition: successor(x) is defined
    x = successor(x);
}

template<typename I>
    requires(Iterator(I))
const I operator+(I f, DistanceType(I) n)
{
    // Precondition: n >= 0 && weak_range(f, n)
    while (!zero(n)) {
        f = successor(f);
        n = predecessor(n);
    }
    return f;
}

template<typename I>
    requires(Iterator(I))
DistanceType(I) operator-(I l, I f)
{
    // Precondition: bounded_range(f, l)
    DistanceType(I) n(0);
    while (f != l) {
        n = successor(n);
        f = successor(f);
    }
    return n;
}

template<typename I, typename Proc>
    requires(Iterator(I) && Readable(I) &&
        Procedure(Proc) && Arity(Op) = 1 &&
        ValueType(I) == InputType(Proc, 0))
Proc my_for_each(I f, I l, Proc proc)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l) {
        proc(source(f));
        f = successor(f);
    }
    return proc;
}

template<typename I>
    requires(Iterator(I) && Readable(I))
I my_find(I f, I l, const ValueType(I)& x)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && source(f) != x) f = successor(f);
    return f;
}

template<typename I>
    requires(Iterator(I) && Readable(I))
I my_find_not(I f, I l, const ValueType(I)& x)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && source(f) == x) f = successor(f);
    return f;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_find_if(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && !p(source(f))) f = successor(f);
    return f;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_find_if_not(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && p(source(f))) f = successor(f);
    return f;
}

//
// Start Exercise 6.1
/////

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_all(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    return my_find_if_not(f, l, p) == l;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_none(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    return my_find_if(f, l, p) == l;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_not_all(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    return my_find_if_not(f, l, p) != l;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_some(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    return my_find_if(f, l, p) != l;
}

//
// End of Exercise 6.1
/////

//
// Start Exercise 6.2
/////

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
class my_count_if_accumulator
{
public:
    my_count_if_accumulator(P p, J j) : p(p), j(j) {}

    void operator()(const ValueType(I)& x)
    {
        if (p(x)) j = successor(j);
    }

    J count() const {
        return j;
    }

private:
    P p;
    J j;
};

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
J my_count_if_2(I f, I l, P p, J j)
{
    // Precondition: readable_bounded_range(f, l)
    return my_for_each(f,
                       l,
                       my_count_if_accumulator<I, P, J>(p, j)).count();
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
DistanceType(I) my_count_if_2(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    typedef DistanceType(I) N;
    return my_for_each(f,
                       l,
                       my_count_if_accumulator<I, P, N>(p, N(0))).count();
}

//
// End Exercise 6.2
/////

template<typename I, typename J>
    requires(Iterator(I) && Readable(I) && Iterator(J))
J my_count(I f, I l, const ValueType(I)& x, J j)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l) {
        if (source(f) == x) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<typename I>
    requires(Iterator(I) && Readable(I))
DistanceType(I) my_count(I f, I l, const ValueType(I)& x)
{
    // Precondition: readable_bounded_range(f, l)
    return my_count(f, l, x, DistanceType(I)(0));
}

template<typename I, typename J>
    requires(Iterator(I) && Readable(I) && Iterator(J))
J my_count_not(I f, I l, const ValueType(I)& x, J j)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l) {
        if (source(f) != x) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<typename I>
    requires(Iterator(I) && Readable(I))
DistanceType(I) my_count_not(I f, I l, const ValueType(I)& x)
{
    // Precondition: readable_bounded_range(f, l)
    return my_count_not(f, l, x, DistanceType(I)(0));
}

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
J my_count_if(I f, I l, P p, J j)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l) {
        if (p(source(f))) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
DistanceType(I) my_count_if(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    return my_count_if(f, l, p, DistanceType(I)(0));
}

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
J my_count_if_not(I f, I l, P p, J j)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l) {
        if (!p(source(f))) j = successor(j);
        f = successor(f);
    }
    return j;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
DistanceType(I) my_count_if_not(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    return my_count_if_not(f, l, p, DistanceType(I)(0));
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
Domain(Op) my_reduce_nonempty(I f, I l, Op op, F fun)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     f != l
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open bounded range
    Domain(Op) r = fun(f);
    f = successor(f);
    while (f != l) {
        r = op(r, fun(f));
        f = successor(f);
    }
    return r;
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
Domain(Op) my_reduce(I f, I l, Op op, F fun, const Domain(Op)& z)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open bounded range
    if (f == l) return z;
    return my_reduce_nonempty(f, l, op, fun);
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
Domain(Op) my_reduce_nonzeros(I f, I l, Op op, F fun, const Domain(Op)& z)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open bounded range
    Domain(Op) x;
    do {
        if (f == l) return z;
        x = fun(f);
        f = successor(f);
    } while (x == z);
    while (f != l) {
        Domain(Op) y = fun(f);
        if (y != z) x = op(x, y);
        f = successor(f);
    }
    return x;
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
Domain(Op) my_reduce_nonempty(I f, DistanceType(I) n, Op op, F fun)
{
    // Preconditions:
    //     weak_range(f, n)
    //     n > 0
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open weak range
    Domain(Op) r = fun(f);
    f = successor(f);
    n = predecessor(n);
    while (!zero(n)) {
        r = op(r, fun(f));
        f = successor(f);
        n = predecessor(n);
    }
    return r;
}

template<typename I, typename Proc>
    requires(Iterator(I) && Readable(I) &&
        Procedure(Proc) && Arity(Op) = 1 &&
        ValueType(I) == InputType(Proc, 0))
pair<Proc, I> my_for_each_n(I f, DistanceType(I) n, Proc proc)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n)) {
        n = predecessor(n);
        proc(source(f));
        f = successor(f);
    }
    return pair<Proc, I>(proc, f);
}

template<typename I>
    requires(Iterator(I) && Readable(I))
pair<I, DistanceType(I)> my_find_n(I f,
                                   DistanceType(I) n,
                                   const ValueType(I)& x)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n) && source(f) != x) {
        n = predecessor(n);
        f = successor(f);
    }
    // n is necessary to determine whether the search succeeded
    // f is necessary to continue / restart the search
    return pair<I, DistanceType(I)>(f, n);
}

template<typename I>
    requires(Iterator(I) && Readable(I))
pair<I, DistanceType(I)> my_find_not_n(I f,
                                       DistanceType(I) n,
                                       const ValueType(I)& x)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n) && source(f) == x) {
        n = predecessor(n);
        f = successor(f);
    }
    return pair<I, DistanceType(I)>(f, n);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, DistanceType(I)> my_find_if_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n) && !p(source(f))) {
        n = predecessor(n);
        f = successor(f);
    }
    return pair<I, DistanceType(I)>(f, n);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, DistanceType(I)> my_find_if_not_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n) && p(source(f))) {
        n = predecessor(n);
        f = successor(f);
    }
    return pair<I, DistanceType(I)>(f, n);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<bool, I> my_all_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    pair<I, DistanceType(I)> q = my_find_if_not_n(f, n, p);
    return pair<bool, I>(zero(q.second), q.first);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<bool, I> my_none_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    pair<I, DistanceType(I)> q = my_find_if_n(f, n, p);
    return pair<bool, I>(zero(q.second), q.first);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<bool, I> my_not_all_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    pair<I, DistanceType(I)> q = my_find_if_not_n(f, n, p);
    return pair<bool, I>(!zero(q.second), q.first);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<bool, I> my_some_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    pair<I, DistanceType(I)> q = my_find_if_n(f, n, p);
    return pair<bool, I>(!zero(q.second), q.first);
}

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
pair<J, I> my_count_if_n_2(I f, DistanceType(I) n, P p, J j)
{
    // Precondition: readable_weak_range(f, n)
    pair<my_count_if_accumulator<I, P, J>, I> q =
        my_for_each_n(f,
                      n,
                      my_count_if_accumulator<I, P, J>(p, j));
    return pair<J, I>(q.first.count(), q.second);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<DistanceType(I), I> my_count_if_n_2(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    typedef DistanceType(I) N;
    pair<my_count_if_accumulator<I, P, N>, I> q =
        my_for_each_n(f,
                      n,
                      my_count_if_accumulator<I, P, N>(p, N(0)));
    return pair<N, I>(q.first.count(), q.second);
}

template<typename I, typename J>
    requires(Iterator(I) && Readable(I) && Iterator(J))
pair<J, I> my_count_n(I f, DistanceType(I) n, const ValueType(I)& x, J j)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n)) {
        if (source(f) == x) j = successor(j);
        n = predecessor(n);
        f = successor(f);
    }
    return pair<J, I>(j, f);
}

template<typename I>
    requires(Iterator(I) && Readable(I))
pair<DistanceType(I), I> my_count_n(I f, DistanceType(I) n, const ValueType(I)& x)
{
    // Precondition: readable_weak_range(f, n)
    return my_count_n(f, n, x, DistanceType(I)(0));
}

template<typename I, typename J>
    requires(Iterator(I) && Readable(I) && Iterator(J))
pair<J, I> my_count_not_n(I f, DistanceType(I) n, const ValueType(I)& x, J j)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n)) {
        if (source(f) != x) j = successor(j);
        n = predecessor(n);
        f = successor(f);
    }
    return pair<J, I>(j, f);
}

template<typename I>
    requires(Iterator(I) && Readable(I))
pair<DistanceType(I), I> my_count_not_n(I f, DistanceType(I) n, const ValueType(I)& x)
{
    // Precondition: readable_weak_range(f, n)
    return my_count_not_n(f, n, x, DistanceType(I)(0));
}

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
pair<J, I> my_count_if_n(I f, DistanceType(I) n, P p, J j)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n)) {
        if (p(source(f))) j = successor(j);
        n = predecessor(n);
        f = successor(f);
    }
    return pair<J, I>(j, f);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<DistanceType(I), I> my_count_if_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    return my_count_if_n(f, n, p, DistanceType(I)(0));
}

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
pair<J, I> my_count_if_not_n(I f, DistanceType(I) n, P p, J j)
{
    // Precondition: readable_weak_range(f, n)
    while (!zero(n)) {
        if (!p(source(f))) j = successor(j);
        n = predecessor(n);
        f = successor(f);
    }
    return pair<J, I>(j, f);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<DistanceType(I), I> my_count_if_not_n(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    return my_count_if_not_n(f, n, p, DistanceType(I)(0));
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
pair<Domain(Op), I> my_reduce_nonempty_n(I f,
                                         DistanceType(I) n,
                                         Op op,
                                         F fun)
{
    // Preconditions:
    //     weak_range(f, n)
    //     n > 0
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open weak range
    Domain(Op) r = fun(f);
    n = predecessor(n);
    f = successor(f);
    while (!zero(n)) {
        r = op(r, fun(f));
        n = predecessor(n);
        f = successor(f);
    }
    return pair<Domain(Op), I>(r, f);
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
pair<Domain(Op), I> my_reduce_n(I f,
                                DistanceType(I) n,
                                Op op,
                                F fun,
                                const Domain(Op)& z)
{
    // Preconditions:
    //     weak_range(f, n)
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open weak range
    if (zero(n)) return pair<Domain(Op), I>(z, f);
    return my_reduce_nonempty_n(f, n, op, fun);
}

template<typename I, typename Op, typename F>
    requires(Iterator(I) && BinaryOperation(Op) &&
        UnaryFunction(F) &&
        I == Domain(F) && Codomain(F) == Domain(Op))
pair<Domain(Op), I> my_reduce_nonzeros_n(I f,
                                         DistanceType(I) n,
                                         Op op,
                                         F fun,
                                         const Domain(Op)& z)
{
    // Preconditions:
    //     weak_range(f, n)
    //     partially_associative(op)
    //     fun is defined on each iterator in
    //       the half-open weak range
    Domain(Op) x;
    do {
        if (zero(n)) return pair<Domain(Op), I>(z, f);
        x = fun(f);
        n = predecessor(n);
        f = successor(f);
    } while (x == z);
    while (!zero(n)) {
        Domain(Op) y = fun(f);
        if (y != z) x = op(x, y);
        n = predecessor(n);
        f = successor(f);
    }
    return pair<Domain(Op), I>(x, f);
}

template<typename I, typename P>
    requires(Iterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
I my_find_if_guarded(I f, P p)
{
    // Preconditions:
    //     there exists some l such that:
    //         bounded_range(f, l)
    //         p(l)
    while (!p(source(f))) f = successor(f);
    return f;
    // Postcondition: p(source(f))
}

template<typename I, typename P>
    requires(Iterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
I my_find_if_not_guarded(I f, P p)
{
    // Preconditions:
    //     there exists some l such that:
    //         bounded_range(f, l)
    //         !p(l)
    while (p(source(f))) f = successor(f);
    return f;
    // Postcondition: !p(source(f))
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) && Relation(R) &&
        ValueType(I0) == ValueType(I1) &&
        ValueType(I0) == Domain(r))
pair<I0, I1> my_find_mismatch(I0 f0, I0 l0, I1 f1, I1 l1, R r)
{
    // Preconditions:
    //     readable_bounded_range(f0, l0)
    //     readable_bounded_range(f1, l1)
    while (f0 != l0 && f1 != l1 && r(source(f0), source(f1))) {
        f0 = successor(f0);
        f1 = successor(f1);
    }
    // Note: we return the final values of both iterators so that
    // (a) we can determine whether a mismatch was found
    //     (a mismatch was found if the lhs doesn't match the original value
    //     of l0 and the rhs doesn't match the original value of l1)
    // (b) in the case where either a mismatch was found, we can continue
    //     the search with the same ranges
    // (c) in the case where a mismatch was not found but one range was shorter
    //     than the other, we can determine where in the longer range the
    //     search terminated
    return pair<I0, I1>(f0, f1);
    // Postcondition:
    //     f0 == l0 || f1 == l1 || !r(source(f0), source(f1))
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) && Relation(R) &&
        ValueType(I0) == ValueType(I1) &&
        ValueType(I0) == Domain(r))
pair<I0, I1> my_find_mismatch_n0(I0 f0, DistanceType(I0) n0, I1 f1, I1 l1, R r)
{
    // Preconditions:
    //     readable_weak_range(f0, n0)
    //     readable_bounded_range(f1, l1)
    while (!zero(n0) && f1 != l1 && r(source(f0), source(f1))) {
        n0 = predecessor(n0);
        f0 = successor(f0);
        f1 = successor(f1);
    }
    return pair<I0, I1>(f0, f1);
    // Postcondition:
    //     zero(n0) || f1 == l1 || !r(source(f0), source(f1))
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) && Relation(R) &&
        ValueType(I0) == ValueType(I1) &&
        ValueType(I0) == Domain(r))
pair<I0, I1> my_find_mismatch_n1(I0 f0, I0 l0, I1 f1, DistanceType(I1) n1, R r)
{
    // Preconditions:
    //     readable_bounded_range(f0, l0)
    //     readable_weak_range(f1, n1)
    while (f0 != l0 && !zero(n1) && r(source(f0), source(f1))) {
        f0 = successor(f0);
        n1 = predecessor(n1);
        f1 = successor(f1);
    }
    return pair<I0, I1>(f0, f1);
    // Postcondition:
    //     f0 == l0 || zero(n1) || !r(source(f0), source(f1))
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) && Relation(R) &&
        ValueType(I0) == ValueType(I1) &&
        ValueType(I0) == Domain(r))
pair<I0, I1> my_find_mismatch_n0_n1(I0 f0,
                                    DistanceType(I0) n0,
                                    I1 f1,
                                    DistanceType(I1) n1,
                                    R r)
{
    // Preconditions:
    //     readable_weak_range(f0, n0)
    //     readable_weak_range(f1, n1)
    while (!zero(n0) && !zero(n1) && r(source(f0), source(f1))) {
        n0 = predecessor(n0);
        f0 = successor(f0);
        n1 = predecessor(n1);
        f1 = successor(f1);
    }
    return pair<I0, I1>(f0, f1);
    // Postcondition:
    //     zero(n0) || zero(n1) || !r(source(f0), source(f1))
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
I my_find_adjacent_mismatch(I f, I l, R r)
{
    // Precondition: readable_bounded_range(f, l)
    if (f == l) return f;
    ValueType(I) x = source(f);
    f = successor(f);
    while (f != l && r(x, source(f))) {
        // This is ok because source must be regular
        // (only successor might not be regular)
        x = source(f);
        f = successor(f);
    }
    return f;
    // Postcondition: f == l || !r(x, source(f))
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
pair<DistanceType(I), I> my_find_adjacent_mismatch_n(I f, DistanceType(I) n, R r)
{
    // Precondition: readable_weak_range(f, n)
    if (zero(n)) return pair<DistanceType(I), I>(n, f);
    ValueType(I) x = source(f);
    n = predecessor(n);
    f = successor(f);
    while (!zero(n) && r(x, source(f))) {
        // This is ok because source must be regular
        // (only successor might not be regular)
        x = source(f);
        n = predecessor(n);
        f = successor(f);
    }
    return pair<DistanceType(I), I>(n, f);
    // Postcondition: zero(n) || !r(x, source(f))
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
bool my_relation_preserving(I f, I l, R r)
{
    // Precondition: readable_bounded_range(f, l)
    return my_find_adjacent_mismatch(f, l, r) == l;
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
pair<bool, I> my_relation_preserving_n(I f, DistanceType(I) n, R r)
{
    // Precondition: readable_weak_range(f, n)
    pair<DistanceType(I), I> q = my_find_adjacent_mismatch_n(f, n, r);
    return pair<bool, I>(q.first == DistanceType(I)(0), q.second);
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
bool my_strictly_increasing_range(I f, I l, R r)
{
    // Preconditions:
    //     readable_bounded_range(f, l)
    //     weak_ordering(r)
    return my_relation_preserving(f, l, r);
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
pair<bool, I> my_strictly_increasing_range_n(I f, DistanceType(I) n, R r)
{
    // Preconditions:
    //     readable_weak_range(f, n)
    //     weak_ordering(r)
    return my_relation_preserving_n(f, n, r);
}

template<typename R>
    requires(Relation(R))
struct complement_of_converse
{
    typedef Domain(R) T;
    R r;
    complement_of_converse(const R& r) : r(r) {}
    bool operator()(const T& a, const T& b)
    {
        return !r(b, a);
    }
};

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
bool my_increasing_range(I f, I l, R r)
{
    // Preconditions:
    //     readable_bounded_range(f, l)
    //     weak_ordering(r)
    return my_relation_preserving(f, l, complement_of_converse<R>(r));
}

template<typename I, typename R>
    requires(Readable(I) && Iterator(I) && Relation(R) &&
        ValueType(I) == Domain(R))
pair<bool, I> my_increasing_range_n(I f, DistanceType(I) n, R r)
{
    // Preconditions:
    //     readable_weak_range(f, n)
    //     weak_ordering(r)
    return my_relation_preserving_n(f, n, complement_of_converse<R>(r));
}

template<typename I, typename P>
    requires(Readable(I) && Iterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
bool my_partitioned(I f, I l, P p)
{
    // Preconditions:
    //    readable_bounded_range(f, l)
    return l == my_find_if_not(my_find_if(f, l, p), l, p);
}

template<typename I, typename P>
    requires(Readable(I) && Iterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
pair<bool, I> my_partitioned_n(I f, DistanceType(I) n, P p)
{
    // Preconditions:
    //    readable_bounded_range(f, l)
    pair<I, DistanceType(I)> q;
    q = my_find_if_n(f, n, p);
    q = my_find_if_not_n(q.first, q.second, p);
    return pair<bool, I>(zero(q.second), q.first);
}

template<typename I, typename R>
    requires(Readable(I) && ForwardIterator(I) &&
        Relation(R) && ValueType(I) == Domain(R))
I my_find_adjacent_mismatch_forward(I f, I l, R r)
{
    // Precondition: readable_bounded_range(f, l)
    if (f == l) return f;
    I t;
    do {
        t = f;
        f = successor(f);
    } while (f != l && r(source(t), source(f)));
    return f;
    // Postcondition: f == l || !r(t, f)
}

template<typename I, typename R>
    requires(Readable(I) && ForwardIterator(I) &&
        Relation(R) && ValueType(I) == Domain(R))
pair<DistanceType(I), I> my_find_adjacent_mismatch_forward_n(I f, DistanceType(I) n, R r)
{
    // Precondition: readable_weak_range(f, n)
    if (zero(n)) return pair<DistanceType(I), I>(n, f);
    I t;
    do {
        t = f;
        n = predecessor(n);
        f = successor(f);
    } while (!zero(n) && r(source(t), source(f)));
    return pair<DistanceType(I), I>(n, f);
    // Postcondition: zero(n) || !r(source(t), source(f))
}

template<typename I, typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_point_n(I f, DistanceType(I) n, P p)
{
    // Preconditions:
    //     readable_counted_range(f, l)
    //     my_partitioned_n(f, n, p)
    //
    // Claims:
    //
    // 1. If n > 0 at the beginning of the loop, then
    //    n >= 0 at the end of the loop.
    //
    //   Proof. Let m = half(n).  If n > 0, then m > 0 and
    //          n - m > 0, i.e. predecessor(n - m) >= 0. Since
    //          we only update the value of n to either m or
    //          predecessor(n - m), it follows that n >= 0
    //          holds at the end of the loop.
    //
    // 2. If [[f, n]] contains the partition point at the
    //    beginning of the loop, then [[f, n]] contains the
    //    partition point at the end of the loop.
    //
    //   Proof. Let m = half(n), and let i = f + m.  If p(source(i)),
    //          then none of the iterators that follow i can
    //          be the partition point; thus [[f, m]] contains
    //          the partition point, and updating n to m keeps
    //          the invariant that [[f, n]] contains the
    //          partition point.  Otherwise, if !p(source(i)), then
    //          none of the iterators in [f, i] can be the
    //          partition point; thus setting f to successor(i)
    //          again preserves the invariant that [[f, n]]
    //          contains the partition point.
    //
    // 3. If my_partition_point_n terminates, then f is the
    //    partition point of the original (p-partitioned) input
    //    range.
    //
    //   Proof. By (2), after the while loop terminates,
    //          [[f, n]] contains the partition point.  But
    //          n = 0 holds after the while loop terminates;
    //          thus [[f, n]] = [[f, 0]] contains the single
    //          iterator f, which must be the partition point.
    //
    // 4. my_partition_point_n terminates.
    //
    //   Proof. Let m = half(n).  Since m < n and
    //          predecessor(n - m) < n, it follows that n
    //          decreases after every iteration of the while
    //          loop.  By (1), n is always nonnegative, and
    //          since n is an integer, n can only decrease
    //          a finite number of times before zero(n) holds.
    //          We conclude that my_partition_point_n performs
    //          only finitely many iterations of the while
    //          loop, ie. my_partition_point_n must terminate.
    //
    // Lemma 6.9. my_partition_point_n returns the partition
    // point of the original (p-partitioned) input range.
    //
    //   Proof. This follows immediately from (3) and (4).
    I i;
    while (!zero(n)) {
        DistanceType(I) m = half(n);
        I i = f + m;
        if (p(source(i))) {
            n = m;
        } else {
            n = n - successor(m);
            f = successor(i);
        }
    }
    return f;
}

template<typename I, typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_point(I f, I l, P p)
{
    // Preconditions:
    //     readable_bounded_range(f, l)
    //     my_partitioned(f, l, p)
    return my_partition_point_n(f, l - f, p);
}

template<typename R>
struct input_type<complement_of_converse<R>, 0> {
    typedef Domain(R) type;
};

template<typename T>
struct input_type<less<T>, 0> {
    typedef T type;
};

template<typename T>
struct input_type<plus<T>, 0> {
    typedef T type;
};

template<typename T>
struct input_type<multiplies<T>, 0> {
    typedef T type;
};

int main() {
    int* x = new int[10];
    for (int i = 0; i < 10; i++) {
        x[i] = i;
    }
    cout << my_partition_point(x, x + 10, bind2nd(greater_equal<int>(), 6)) - x << endl;
    delete[] x;
}
