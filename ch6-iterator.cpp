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
    for (int i = 0; i < 5; i++) {
        x[i] = i + 1;
        x[5 + i] = i + 1;
    }
    int (*fun)(int*) = source<int>;
    pair<int, int*> q =  my_reduce_nonzeros_n(x, 10, multiplies<int>(), fun, 1);
    cout << "result: " << q.first << ", pos: " << (q.second - x) << endl;
    // pair<int, int*> q = my_count_if_not_n(x, 10, bind2nd(less<int>(), 3));
    // cout << "count: " << q.first << ", pos: " << (q.second - x) << endl;
    delete[] x;
}
