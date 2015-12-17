#ifndef MY_REARRANGEMENT
#define MY_REARRANGEMENT

#include <cassert>
#include "my_copy.h"
#include "my_division.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_type_functions.h"

using namespace std;

template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) &&
        I == Domain(F))
void my_cycle_to(I i, F f)
{
    // Preconditions:
    //     the orbit of i under f is circular
    //     for all n in N, deref(f^i(n)) is defined
    I k = f(i);
    while (k != i) {
        exchange_values(i, k);
        k = f(k);
    }
}

template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) &&
        I == Domain(F))
void my_cycle_from(I i, F f)
{
    // Preconditions:
    //     the orbit of i under f is circular
    //     for all n in N, deref(f^i(n)) is defined
    I j = i;
    I k = f(i);
    if (k == i) return;
    ValueType(I) tmp = source(i);
    while (k != i) {
        sink(j) = source(k);
        j = k;
        k = f(k);
    }
    sink(j) = tmp;
}

//
// Begin Exercise 10.4
/////

template<typename I, typename F>
    requires(Transformation(F) && I == Domain(F))
void my_cycle_moved(I f, I i, F p, bool* moved)
{
    // Preconditions:
    //     the orbit of i under p is circular
    //     for all n in N, bounded_range(f, p^n(i))
    //     for all n in N, p^n(i) - f < k, where k
    //         is the size of the moved array
    moved[i - f] = true;
    I k = p(i);
    while (k != i) {
        moved[k - f] = true;
        k = p(k);
    }
}

template<typename I, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == Domain(F))
void my_rearrange_to(I f, I l, F to)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     to is a permutation of the input range
    bool* moved = new bool[l - f];
    I i = f;
    while (i != l) {
        if (!moved[i - f]) {
            my_cycle_to(i, to);
            my_cycle_moved(f, i, to, moved);
        }
        i = successor(i);
    }
    delete[] moved;
}

template<typename I, typename N, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Integer(N) && Transformation(F) &&
        I == Domain(F))
void my_rearrange_to_n(I f, N n, F to)
{
    // Preconditions:
    //     mutable_counted_range(f, n)
    //     to is a permutation of the input range
    my_rearrange_to(f, f + n, to);
}

template<typename I, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == Domain(F))
void my_rearrange_from(I f, I l, F from)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     to is a permutation of the input range
    bool* moved = new bool[l - f];
    I i = f;
    while (i != l) {
        if (!moved[i - f]) {
            my_cycle_from(i, from);
            my_cycle_moved(f, i, from, moved);
        }
        i = successor(i);
    }
    delete[] moved;
}

template<typename I, typename N, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Integer(N) && Transformation(F) &&
        I == Domain(F))
void my_rearrange_from_n(I f, N n, F from)
{
    // Preconditions:
    //     mutable_counted_range(f, n)
    //     from is a permutation of the input range
    my_rearrange_from(f, f + n, from);
}

//
// End Exercise 10.4
/////

//
// Begin Exercise 10.5
/////

template<typename I, typename F, typename R>
    requires(Transformation(F) && I == Domain(F) &&
        BinaryRelation(R) && I == Domain(R))
bool cycle_representative(I i, F f, R r)
{
    // Preconditions:
    //     the orbit of i under f is circular
    //     total_ordering(r)
    I k = f(i);
    while (k != i) {
        if (r(k, i)) return false;
        k = f(k);
    }
    return true;
}

template<typename I, typename F, typename R>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == Domain(F) &&
        BinaryRelation(R) && I == Domain(R))
void my_rearrange_to(I f, I l, F to, R r)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     to is a permutation of the input range
    //     total_ordering(r)
    I i = f;
    while (i != l) {
        if (cycle_representative(i, to, r)) my_cycle_to(i, to);
        i = successor(i);
    }
}

template<typename I, typename N, typename F, typename R>
    requires(Mutable(I) && IndexedIterator(I) &&
        Integer(N) &&
        Transformation(F) && I == Domain(F) &&
        BinaryRelation(R) && I == Domain(R))
void my_rearrange_to_n(I f, N n, F to, R r)
{
    // Preconditions:
    //     mutable_counted_range(f, n)
    //     to is a permutation of the input range
    //     total_ordering(r)
    my_rearrange_to(f, f + n, to, r);
}

template<typename I, typename F, typename R>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == Domain(F) &&
        BinaryRelation(R) && I == Domain(R))
void my_rearrange_from(I f, I l, F from, R r)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     to is a permutation of the input range
    //     total_ordering(r)
    I i = f;
    while (i != l) {
        if (cycle_representative(i, from, r)) my_cycle_from(i, from);
        i = successor(i);
    }
}

template<typename I, typename N, typename F, typename R>
    requires(Mutable(I) && IndexedIterator(I) &&
        Integer(N) &&
        Transformation(F) && I == Domain(F) &&
        BinaryRelation(R) && I == Domain(R))
void my_rearrange_from_n(I f, N n, F from, R r)
{
    // Preconditions:
    //     mutable_counted_range(f, n)
    //     from is a permutation of the input range
    //     total_ordering(r)
    my_rearrange_from(f, f + n, from, r);
}

//
// End Exercise 10.5
/////

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
void my_reverse_n_indexed(I f, DistanceType(I) n)
{
    // Precondition: mutable_counted_range(f, n)
    DistanceType(I) i(0);
    n = predecessor(n);
    while (i < n) {
        exchange_values(f + i, f + n);
        i = successor(i);
        n = predecessor(n);
    }
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
void my_reverse_indexed(I f, I l)
{
    // Precondition: mutable_bounded_range(f, n)
    return my_reverse_n_indexed(f, l - f);
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
void my_reverse_bidirectional(I f, I l)
{
    // Precondition: mutable_bounded_range(f, l)
    while (true) {
        if (f == l) return;
        l = predecessor(l);
        if (f == l) return;
        exchange_values(f, l);
        f = successor(f);
    }
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
void my_reverse_n_bidirectional(I f, I l, DistanceType(I) n)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     0 <= n < l - f
    my_reverse_swap_ranges_n(l, f, half_nonnegative(n));
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
I my_reverse_n_with_buffer(I f_i, DistanceType(I) n, B f_b)
{
    // Preconditions:
    //     readable_counted_range(f_i, n)
    //     writable_counted_range(f_b, n)
    return my_reverse_copy(f_b, my_copy_n(f_i, n, f_b).second, f_i);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I my_reverse_n_forward(I f, DistanceType(I) n)
{
    typedef DistanceType(I) N;
    if (n == N(0)) return f;
    if (n == N(1)) return successor(f);
    N h = half_nonnegative(n);
    I m = my_reverse_n_forward(f, h);
    if (odd(n)) m = successor(m);
    I l = my_reverse_n_forward(m, h);
    my_swap_ranges_n(f, m, h);
    return l;
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
I my_reverse_n_adaptive(I f_i, DistanceType(I) n_i, B f_b, DistanceType(B) n_b)
{
    // Preconditions:
    //     mutable_counted_range(f_i, n_i)
    //     mutable_counted_range(b_b, n_b)
    typedef DistanceType(I) N;
    if (n_i == N(0)) return f_i;
    if (n_i == N(1)) return successor(f_i);
    if (n_i <= n_b)  return my_reverse_n_with_buffer(f_i, n_i, f_b);
    N h_i = half_nonnegative(n_i);
    I m_i = my_reverse_n_adaptive(f_i, h_i, f_b, n_b);
    if (odd(n_i)) m_i = successor(m_i);
    I l_i = my_reverse_n_adaptive(m_i, h_i, f_b, n_b);
    my_swap_ranges_n(f_i, m_i, h_i);
    return l_i;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I my_reverse_n_with_temporary_buffer(I f, DistanceType(I) n)
{
    pair<ValueType(I)*, ptrdiff_t> b = get_temporary_buffer< ValueType(I) >(n);
    I l = my_reverse_n_adaptive(f, n, b.first, b.second);
    return_temporary_buffer(b.first);
    return l;
}

template<typename I>
    requires(RandomAccessIterator(I))
struct k_rotate_from_permutation_random_access
{
    DistanceType(I) k;
    DistanceType(I) n_minus_k;
    I m_prime;
    k_rotate_from_permutation_random_access(I f, I m, I l) :
        k(l - m), n_minus_k(m - f), m_prime(f + (l - m))
    {
        // Preconditions:
        //     bounded_range(f, l)
        //     m in [f, l)
    }
    I operator()(I x)
    {
        // Precondition: x in [f, l)
        if (x < m_prime) return x + n_minus_k;
        else             return x - k;
    }
};

template<typename I>
    requires(IndexedIterator(I))
struct k_rotate_from_permutation_indexed
{
    DistanceType(I) k;
    DistanceType(I) n_minus_k;
    I f;
    k_rotate_from_permutation_indexed(I f, I m, I l) :
        k(l - m), n_minus_k(m - f), f(f)
    {
        // Preconditions:
        //     bounded_range(f, l)
        //     m in [f, l)
    }
    I operator()(I x)
    {
        // Precondition: x in [f, l)
        DistanceType(I) i = x - f;
        if (i < k) return x + n_minus_k;
        else       return f + (i - k);
    }
};

template<typename I, typename F>
    requires(Mutable(I) && IndexedIterator(I) &&
        Transformation(F) && I == Domain(F))
I my_rotate_cycles(I f, I m, I l, F from)
{
    typedef DistanceType(I) N;
    N d = gcd(m - f, l - m);
    while (count_down(d)) my_cycle_from(f + d, from);
    return f + (l - m);
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
I rotate_indexed_nontrivial(I f, I m, I l)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     m in [f, l)
    //     f precedes m, m precedes l
    k_rotate_from_permutation_indexed<I> p(f, m, l);
    return my_rotate_cycles(f, m, l, p);
}

template<typename I>
    requires(Mutable(I) && RandomAccessIterator(I))
I rotate_random_access_nontrivial(I f, I m, I l)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     m in [f, l)
    //     f precedes m, m precedes l
    k_rotate_from_permutation_random_access<I> p(f, m, l);
    return my_rotate_cycles(f, m, l, p);
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
I rotate_bidirectional_nontrivial(I f, I m, I l)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    my_reverse_bidirectional(f, m);
    my_reverse_bidirectional(m, l);
    pair<I, I> p = my_reverse_swap_ranges_bounded(m, l, f, m);
    my_reverse_bidirectional(p.second, p.first);
    if (m == p.second) return p.first;
    else               return p.second;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void rotate_forward_annotated(I f, I m, I l)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
                                             DistanceType(I) a = m - f;
                                             DistanceType(I) b = l - m;
    while (true) {
        pair<I, I> p = my_swap_ranges_bounded(f, m, m, l);
        if (m == p.first && l == p.second) { assert(a == b);
            return;
        }
        f = p.first;
        if (f == m) {                        assert (b > a);
            m = p.second;                    b = b - a;
        } else {                             assert(a > b);
                                             a = a - b;
        }
    }
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
void rotate_forward_step(I& f, I& m, I l)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     f precedes m, m precedes l
    I c = m;
    do {
        // Calling my_swap_step until either
        // f == m or c == l is equivalent to
        // calling my_swap_ranges_bounded(f, m, m, l);
        my_swap_step(f, c);
        // Since f and c are the limits of the swapped
        // subranges, if a call to my_swap_ranges_bounded
        // would have returned p then whenever one of
        // f == m or c == l holds, we would also have
        // p.m0 == f and p.m1 == c
        if (f == m) m = c; // This is equivalent to the assignment
                           // m = p.m1 in rotate_forward_annotated;
                           // in the case c != l, continuing at the
                           // beginning of this do... while loop is
                           // equivalent to continuing at the
                           // beginning of the while loop in
                           // rotate_forward_annotated
    } while (c != l);
    // Upon returning, c == l holds, and f == m may or may
    // not hold; if f == m does not hold, then returning
    // from rotate_forward_step is equivalent to entering
    // the else block in rotate_forward_annotated
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_forward_nontrivial(I f, I m, I l)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    rotate_forward_step(f, m, l);
    // By Lemma 10.25 and the fact that rotate_forward_step
    // is equiavlent to iterating through the while loop in
    // rotate_forward_annotated until reaching the else clause,
    // m_prime is the standard return value for rotate
    I m_prime = f;
    // If m == l after rotate_forward_step returns, then
    // f == m would hold, and since m = c is the statement
    // immediately before the while (c != l) check, m == l
    // would also hold; this is the same termination
    // condition as rotate_forward_annotated
    while (m != l) rotate_forward_step(f, m, l);
    return m_prime;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_partial_nontrivial(I f, I m, I l)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    return my_swap_ranges(m, l, f);
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B))
I rotate_with_buffer_nontrivial(I f, I m, I l, B f_b)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    //     mutable_counted_range(f_b, l - f)
    B l_b = my_copy(f, m, f_b);
    I m_prime = my_copy(m, l, f);
    my_copy(f_b, l_b, m_prime);
    return m_prime;
}

template<typename I, typename B>
    requires(Mutable(I) && BidirectionalIterator(I) &&
        Mutable(B) && ForwardIterator(B))
I rotate_with_buffer_nontrivial_backward(I f, I m, I l, B f_b)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    //     mutable_counted_range(f_b, l - f)
    B l_b = my_copy(m, l, f_b);
    my_copy_backward(f, m, l);
    return my_copy(f_b, l_b, f);
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_dispatch(I f, I m, I l)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    if (m == f) return l;
    if (m == l) return f;
    return rotate_nontrivial(f, m, l, IteratorConcept(I)());
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_nontrivial(I f, I m, I l, my_forward_iterator_tag)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    return rotate_forward_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && BidirectionalIterator(I))
I rotate_nontrivial(I f, I m, I l, my_bidirectional_iterator_tag)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    return rotate_bidirectional_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && IndexedIterator(I))
I rotate_nontrivial(I f, I m, I l, my_indexed_iterator_tag)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    return rotate_indexed_nontrivial(f, m, l);
}

template<typename I>
    requires(Mutable(I) && RandomAccessIterator(I))
I rotate_nontrivial(I f, I m, I l, my_random_access_iterator_tag)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    return rotate_random_access_nontrivial(f, m, l);
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
struct my_reverse_n_buffer_adapter
{
    typedef DistanceType(I) N;
    typedef DistanceType(B) N_b;
    I f;
    I l;
    N n;
    B f_b;
    N_b n_b;
    my_reverse_n_buffer_adapter(I f,
                                N n,
                                B f_b,
                                N_b n_b) :
        f(f), n(n), f_b(f_b), n_b(n_b)
    {
        l = my_reverse_n_with_buffer(f, min(N(n), N(n_b)), f_b);
    }
    my_reverse_n_buffer_adapter successor() const
    {
        return my_reverse_n_buffer_adapter(l, max(N(n - n_b), N(0)), f_b, n_b);
    }
};

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
struct distance_type<my_reverse_n_buffer_adapter<I, B> >
{
    typedef unsigned long type;
};

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
my_reverse_n_buffer_adapter<I, B> successor(const my_reverse_n_buffer_adapter<I, B>& x)
{
    return x.successor();
}

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
struct my_reverse_n_buffered_trivial
{
    pair<I, I> operator()(const my_reverse_n_buffer_adapter<I, B>& x)
    {
        return pair<I, I>(x.f, x.l);
    }
};

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
struct my_reverse_n_buffered_op
{
    typedef pair<I, I> T;
    T operator()(const T& x, const T& y)
    {
        assert(x.second == y.first);
        rotate_dispatch(x.first, x.second, y.second);
        return T(x.first, y.second);
    }
};

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
struct input_type<my_reverse_n_buffered_op<I>, 0>
{
    typedef pair<I, I> type;
};

template<typename I, typename B>
    requires(Mutable(I) && ForwardIterator(I) &&
        Mutable(B) && BidirectionalIterator(B) &&
        ValueType(I) == ValueType(B))
I my_reverse_n_adaptive_iterative(I f_i, DistanceType(I) n_i, B f_b, DistanceType(B) n_b)
{
    // Preconditions:
    //     mutable_counted_range(f_i, n_i)
    //     mutable_counted_range(b_b, n_b)
    typedef DistanceType(I) N;
    if (n_i == N(0)) return f_i;
    if (n_i == N(1)) return successor(f_i);
    if (n_i <= n_b)  return my_reverse_n_with_buffer(f_i, n_i, f_b);
    return my_reduce_balanced_n(my_reverse_n_buffer_adapter<I, B>(
                                            f_i,
                                            n_i,
                                            f_b,
                                            n_b),
                                (n_i + (n_b - 1)) / n_b,
                                my_reverse_n_buffered_op<I>(),
                                my_reverse_n_buffered_trivial<I, B>(),
                                pair<I, I>(f_i, f_i)).second;
}

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I my_reverse_n_iterative_with_temporary_buffer(I f, DistanceType(I) n)
{
    pair<ValueType(I)*, ptrdiff_t> b = get_temporary_buffer< ValueType(I) >(n);
    I l = my_reverse_n_adaptive_iterative(f, n, b.first, b.second);
    return_temporary_buffer(b.first);
    return l;
}

#endif
