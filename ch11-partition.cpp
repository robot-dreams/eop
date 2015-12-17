#include <iostream>
#include <stack>
#include "my_copy.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_link.h"
#include "my_rearrangement.h"
#include "my_type_functions.h"
#include "my_test_util.h"

using namespace std;

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && I == Domain(P))
bool my_partitioned_at_point(I f, I l, I i, P p)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     i in [f, l)
    while (f != i) {
        if (p(f)) return false;
        f = successor(f);
    }
    while (f != l) {
        if (!p(f)) return false;
        f = successor(f);
    }
    return true;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_partitioned_at_point_source(I f, I l, I i, P p)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     i in [f, l)
    if (my_find_if(f, l, p) != i) return false;
    return my_find_if_not(i, l, p) == l;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && I == Domain(P))
I potential_partition_point(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    I i = f;
    while (f != l) {
        if (!p(f)) i = successor(i);
        f = successor(f);
    }
    return i;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I potential_partition_point_source(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    predicate_source<I, P> ps(p);
    return potential_partition_point(f, l, ps);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_semistable(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    I i = my_find_if(f, l, p);
    if (i == l) return i;
    I j = successor(i);
    while (true) {
        j = my_find_if_not(i, l, p);
        if (j == l) return i;
        my_swap_step(i, j);
    }
}

//
// Begin Exercise 11.3
/////

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_semistable_2(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    I i = my_find_if(f, l, p);
    if (i == l) return i;
    I j = successor(i);
    while (j != l) {
        if (p(source(j))) j = successor(j);
        else              my_swap_step(i, j);
    }
    return i;
}

//
// End Exercise 11.3
/////

//
// Begin Exercise 11.4
/////

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_remove_if(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    I i = my_find_if(f, l, p);
    // In the case i == l, postcondition (1) is trivially satisfied
    if (i == l) return i;
    I j = successor(i);
    while (j != l) {
        if (p(source(j))) j = successor(j);
        // Since source(j) takes on the value of every element in
        // the range [my_find_if(f, l, p), l), j takes on the value
        // of every element in the range whose source does not
        // satisfy p; furthermore, the order that source(j) takes
        // on these values is the same as the order that the
        // corresponding elements appear in the original input
        // range.
        //
        // Note that when j first becomes equal to an element,
        // that element's value is unchanged from its original
        // value (since i precedes j at every point in this
        // procedure, and the procedure only ever changes the
        // value at i).
        else              my_copy_step(j, i);
    }
    return i;
    // Postcondition:
    //     Let i' be the return value.  Then:
    //         (1) [f, i') contains the values in the original range
    //             not satisfying p, with their relative ordering
    //             preserved (see the comment above)
    //         (2) [i', l) contains the same values as the original
    //             range, since the only statement that changes any
    //             values is my_copy_step(j, i) and i always
    //             precedes i'
}

//
// End Exercise 11.4
/////

//
// Begin Exercise 11.5
/////

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
void my_partition_semistable_3(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    if (f == l) return;
    I i = f;
    while (successor(i) != l && !p(source(i)))
        i = successor(i);
    if (successor(i) == l) return;
    I j = successor(i);
    while (successor(j) != l) {
        if (p(source(j))) j = successor(j);
        else              my_swap_step(i, j);
    }
    my_swap_step(i, j);
}

//
// End Exercise 11.5
/////

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_bidirectional(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    while (true) {
        f = my_find_if(f, l, p);
        l = my_find_backward_if_not(f, l, p);
        if (f == l) return f;
        my_reverse_swap_step(l, f);
    }
}

//
// Begin Exercise 11.6
/////

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_forward(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    I m = potential_partition_point_source(f, l, p);
    while (true) {
        f = my_find_if(f, l, p);
        m = my_find_if_not(m, l, p);
        if (m == l) return f;
        my_swap_step(f, m);
    }
}

//
// End Exercise 11.6
/////

//
// Begin Exercise 11.7
/////

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_bidirectional_single_cycle(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    f = my_find_if(f, l, p);
    if (f == l) return f;
    ValueType(I) tmp = source(f);
    while (true) {
        l = my_find_backward_if_not(f, l, p);
        sink(f) = source(predecessor(l));
        f = my_find_if(f, l, p);
        if (f == l) { sink(predecessor(l)) = tmp; return f; }
        else          sink(predecessor(l)) = source(f);
    }
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_forward_single_cycle(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    I m = potential_partition_point_source(f, l, p);
    if (m == f) return f;
    if (m == l) return l;
    m = my_find_if_not(m, l, p);
    ValueType(I) tmp = source(m);
    while (true) {
        f = my_find_if(f, l, p);
        sink(m) = source(f);
        m = my_find_if_not(m, l, p);
        if (m == l) { sink(f) = tmp; return my_find_if(f, l, p); }
        else          sink(f) = source(m);
    }
}

//
// End Exercise 11.7
/////

//
// Begin Exercise 11.8
/////

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_bidirectional_unguarded(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    f = my_find_if(f, l, p);
    l = my_find_backward_if_not(f, l, p);
    if (f == l) return f;
    while (true) {
        f = my_find_if_unguarded(f, p);
        l = my_find_backward_if_not_unguarded(l, p);
        if (f == l) return f;
        my_reverse_swap_step(l, f);
    }
}

//
// End Exercise 11.8
/////

//
// Begin Exercise 11.9
/////

template<typename I, typename P>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_bidirectional_single_cycle_unguarded(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    f = my_find_if(f, l, p);
    l = my_find_backward_if_not(f, l, p);
    if (f == l) return f;
    ValueType(I) tmp = source(f);
    while (true) {
        sink(f) = source(predecessor(l));
        f = my_find_if_unguarded(f, p);
        if (f == l) { sink(predecessor(l)) = tmp; return f; }
        else          sink(predecessor(l)) = source(f);
        l = my_find_backward_if_not_unguarded(l, p);
    }
}

//
// End Exercise 11.9
/////

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_stable_with_buffer(I f, I l, B f_b, P p)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     mutable_counted_range(f_b, l - f)
    pair<I, B> x = my_partition_copy(f, l, f, f_b, p);
    my_copy(f_b, x.second, x.first);
    return x.first;
}

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_n_with_buffer(I f, DistanceType(I) n, B f_b, P p)
{
    // Preconditions:
    //     mutable_counted_range(f, n)
    //     mutable_counted_range(f_b, n))
    triple<I, I, B> x = my_partition_copy_n(f, n, f, f_b, p);
    return pair<I, I>(x.m1, my_copy(f_b, x.m2, x.m1));
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_singleton(I f, P p)
{
    // Precondition:
    //     readable_bounded_range(f, successor(f))
    I l = successor(f);
    if (!p(source(f))) f = l;
    return pair<I, I>(f, l);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
pair<I, I> my_combine_ranges(const pair<I, I>& x,
                             const pair<I, I>& y)
{
    return pair<I, I>(rotate_dispatch(x.first, x.second, y.first),
                      y.second);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_n_nonempty(I f, DistanceType(I) n, P p)
{
    // Preconditions:
    //     mutable_counted_range(f, n)
    //     n > 0
    if (one(n)) return my_partition_stable_singleton(f, p);
    DistanceType(I) h = half_nonnegative(n);
    pair<I, I> x = my_partition_stable_n_nonempty(f, h, p);
    pair<I, I> y = my_partition_stable_n_nonempty(x.second, n - h, p);
    return my_combine_ranges(x, y);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_n(I f, DistanceType(I) n, P p)
{
    // Precondition:
    //     mutable_counted_range(f, n)
    if (zero(n)) return pair<I, I>(f, f);
    return my_partition_stable_n_nonempty(f, n, p);
}

//
// Begin Exercise 11.10
/////

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_n_nonempty_adaptive(I f_i,
                                                   DistanceType(I) n_i,
                                                   B f_b,
                                                   DistanceType(B) n_b,
                                                   P p)
{
    // Preconditions:
    //     mutable_counted_range(f_i, n_i)
    //     mutable_counted_range(f_b, n_b);
    //     n_i > 0
    if (one(n_i))
        return my_partition_stable_singleton(f_i, p);
    if (n_i <= n_b)
        return my_partition_stable_n_with_buffer(f_i, n_i, f_b, p);
    DistanceType(I) h = half_nonnegative(n_i);
    pair<I, I> x = my_partition_stable_n_nonempty_adaptive(f_i, h, f_b, n_b, p);
    pair<I, I> y = my_partition_stable_n_nonempty_adaptive(x.second, n_i - h, f_b, n_b, p);
    return my_combine_ranges(x, y);
}

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_n_adaptive(I f_i,
                                          DistanceType(I) n_i,
                                          B f_b,
                                          DistanceType(B) n_b,
                                          P p)
{
    // Preconditions:
    //     mutable_counted_range(f_i, n_i)
    //     mutable_counted_range(f_b, n_b);
    if (zero(n_i)) return pair<I, I>(f_i, f_i);
    return my_partition_stable_n_nonempty_adaptive(f_i, n_i, f_b, n_b, p);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_n_with_temporary_buffer(I f, DistanceType(I) n, P p)
{
    // Precondition:
    //     mutable_counted_range(f, n)
    if (zero(n)) return pair<I, I>(f, f);
    if (one(n))  return my_partition_stable_singleton(f, p);
    pair<ValueType(I)*, ptrdiff_t> b = get_temporary_buffer< ValueType(I) >(n);
    pair<I, I> x = my_partition_stable_n_adaptive(f, n, b.first, b.second, p);
    return_temporary_buffer(b.first);
    return x;
}

//
// End Exercise 11.10
/////

template<typename I, typename P>
    requires(Readable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
struct my_partition_trivial
{
    P p;
    my_partition_trivial(P p) : p(p) {}
    pair<I, I> operator()(I i)
    {
        return my_partition_stable_singleton<I, P>(i, p);
    }
};

template<typename I, typename P>
    requires(ForwardIterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
I my_partition_stable_iterative(I f, I l, P p)
{
    // Precondition:
    //     bounded_range(f, l)
    //     l - f < 2^64
    return my_reduce_balanced(f,
                              l,
                              my_combine_ranges<I>,
                              my_partition_trivial<I, P>(p),
                              pair<I, I>(f, f)).first;
}

template<typename I, typename P>
    requires(ForwardIterator(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
I my_partition_stable_n_iterative(I f, DistanceType(I) n, P p)
{
    // Precondition:
    //     counted_range(f, l)
    //     n < 2^64
    return my_reduce_balanced_n(f,
                                n,
                                my_combine_ranges<I>,
                                my_partition_trivial<I, P>(p),
                                pair<I, I>(f, f)).first;
}

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        UnaryPredicate(P) &&
        ValueType(I) == ValueType(B) &&
        ValueType(I) == Domain(P))
struct my_partition_n_buffer_adapter
{
    typedef DistanceType(I) N;
    typedef DistanceType(B) N_b;
    I f;
    pair<I, I> x;
    N n;
    B f_b;
    N_b n_b;
    P p;
    my_partition_n_buffer_adapter(I f,
                                N n,
                                B f_b,
                                N_b n_b,
                                P p) :
        f(f), n(n), f_b(f_b), n_b(n_b), p(p)
    {
        x = my_partition_stable_n_with_buffer(f, min(N(n), N(n_b)), f_b, p);
    }
    my_partition_n_buffer_adapter successor() const
    {
        return my_partition_n_buffer_adapter(x.second,
                                           max(N(n - n_b), N(0)),
                                           f_b,
                                           n_b,
                                           p);
    }
};

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        UnaryPredicate(P) &&
        ValueType(I) == ValueType(B) &&
        ValueType(I) == Domain(P))
struct distance_type<my_partition_n_buffer_adapter<I, B, P> >
{
    typedef unsigned long type;
};

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        UnaryPredicate(P) &&
        ValueType(I) == ValueType(B) &&
        ValueType(I) == Domain(P))
my_partition_n_buffer_adapter<I, B, P>
successor(const my_partition_n_buffer_adapter<I, B, P>& x)
{
    return x.successor();
}

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        UnaryPredicate(P) &&
        ValueType(I) == ValueType(B) &&
        ValueType(I) == Domain(P))
struct my_partition_n_buffered_trivial
{
    pair<I, I> operator()(const my_partition_n_buffer_adapter<I, B, P>& x)
    {
        return x.x;
    }
};

template<typename I, typename B, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && ForwardIterator(B) &&
        ValueType(I) == ValueType(B) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_stable_n_adaptive_iterative(I f,
                                           DistanceType(I) n,
                                           B f_b,
                                           DistanceType(B) n_b,
                                           P p)
{
    // Precondition:
    //     counted_range(f, n)
    //     counted_range(f_b, n_b)
    //     n < 2^64
    return my_reduce_balanced_n(my_partition_n_buffer_adapter<I, B, P>(
                                    f,
                                    n,
                                    f_b,
                                    n_b,
                                    p),
                                (n + (n_b - 1)) / n_b,
                                my_combine_ranges<I>,
                                my_partition_n_buffered_trivial<I, B, P>(),
                                pair<I, I>(f, f)).first;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_stable_n_iterative_with_temporary_buffer(I f,
                                                        DistanceType(I) n,
                                                        P p)
{
    // Precondition:
    //     counted_range(f, n)
    //     counted_range(f_b, n_b)
    //     n < 2^64
    pair<ValueType(I)*, ptrdiff_t> b = get_temporary_buffer< ValueType(I) >(n);
    I m_prime = my_partition_stable_n_adaptive_iterative(f, n, b.first, b.second, p);
    return_temporary_buffer(b.first);
    return m_prime;
}

// Scratch work

template<typename Op>
    requires(BinaryOperation(Op))
struct my_counter_machine_2
{
    typedef Domain(Op) T;
    Op op;
    T z;
    T f[64];
    T* l;
    my_counter_machine_2(Op op, const T& z) : op(op), z(z)
    {
        fill(begin(f), end(f), z);
        l = f;
    }
    void add(T x)
    {
        T* i = f;
        while (i != l) {
            if (source(i) == z) {
                sink(i) = x;
                return;
            }
            x = op(source(i), x);
            sink(i) = z;
            i = successor(i);
        }
        sink(i) = x;
        l = successor(l);
    }
    T combine()
    {
        T x = z;
        T* i = l;
        while (i != f) {
            i = predecessor(i);
            if (source(i) != z) x = op(x, source(i));
        }
        return x;
    }
};

template<typename I, typename Op, typename F>
    requires(Readable(I) && ForwardIterator(I) &&
        BinaryOperation(Op) && UnaryFunction(F) &&
        I == Domain(F) && Domain(Op) == Codomain(F))
Domain(Op) my_reduce_balanced_2(I f, I l, Op op, F fun, const Domain(Op)& z)
{
    my_counter_machine_2<Op> m(op, z);
    while (f != l) {
        m.add(fun(f));
        f = successor(f);
    }
    return m.combine();
}

template<typename I>
    requires(ForwardIterator(I))
struct my_partition_weighted_range
{
    typedef pair<I, I> T;
    stack<pair<T, int> > elements;
    my_partition_weighted_range(T x, int weight = 1)
    {
        elements.push(pair<T, int>(x, weight));
    }
    T combine()
    {
        while (elements.size() > 1) {
            pair<T, int> p_y = elements.top();
            elements.pop();
            pair<T, int> p_x = elements.top();
            elements.pop();
            elements.push(pair<T, int>(my_combine_ranges(p_x.first, p_y.first),
                                       p_x.second + p_y.second));
        }
        return elements.top().first;
    }
    void adjoin(T y)
    {
        int weight = 1;
        while (!elements.empty() && weight == elements.top().second) {
            pair<T, int> p_x = elements.top();
            elements.pop();
            y = my_combine_ranges(p_x.first, y);
            weight = twice(weight);
        }
        elements.push(pair<T, int>(y, weight));
    }
};

template<typename I, typename P>
    requires(Readable(I) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
struct my_partition_trivial_2
{
    P p;
    my_partition_trivial_2(P p) : p(p) {}
    my_partition_weighted_range<I> operator()(I f)
    {
        // Precondition:
        //     mutable_bounded_range(f, successor(f))
        I l = successor(f);
        if (!p(source(f))) f = l;
        return my_partition_weighted_range<I>(pair<I, I>(f, l));
    }
};

template<typename I>
    requires(ForwardIterator(I))
my_partition_weighted_range<I>
my_combine_weighted_ranges(my_partition_weighted_range<I> x,
                           my_partition_weighted_range<I> y)
{
    pair<I, I> p = y.combine();
    x.adjoin(p);
    return x;
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_reduce_0(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    if (f == l) return pair<I, I>(f, f);
    return my_reduce_nonempty(f,
                              l,
                              my_combine_weighted_ranges<I>,
                              my_partition_trivial_2<I, P>(p)).combine();
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<I, I> my_partition_stable_reduce_1(I f, I l, P p)
{
    // Precondition:
    //     mutable_bounded_range(f, l)
    return my_reduce_balanced(f,
                              l,
                              my_combine_ranges<I>,
                              my_partition_trivial<I, P>(p),
                              pair<I, I>(f, f));
}

template<typename T>
struct input_type<plus<T>, 0>
{
    typedef T type;
};

template<typename T>
void print(T x)
{
    cout << x << " ";
}

int main() {

    int n = 100;

    /*
    typedef link_node<int>* I;
    typedef link_node_forward_linker<int> S;

    pair<I, I> p = new_linked_list(n, 1, 1);
    I x = p.first;

    pair<I, I> q = new_linked_list(n, 0, 0);
    I y = q.first;
    */

    int* x = new_array_list(n, 1, 1);
    int* y = new_array_list(n, 0, 0);
    my_for_each(x, x + n, print<int>); cout << endl;
    // my_partition_stable_n_iterative_with_temporary_buffer(x, n, even<int>);
    // my_partition_stable_n(x, n, even<int>);
    my_reverse_n_iterative_with_temporary_buffer(x, n);
    // my_reverse_n_forward(x, n);
    my_for_each(x, x + n, print<int>); cout << endl;

}
