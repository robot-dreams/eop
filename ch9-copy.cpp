#include <iostream>
#include "my_integer.h"
#include "my_iterator.h"
#include "my_intrinsics.h"
#include "my_link.h"
#include "my_type_functions.h"

using namespace std;

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
void my_copy_step(I& f_i, O& f_o)
{
    // Precondition: source(f_i) and sink(f_o) are defined
    sink(f_o) = source(f_i);
    f_i = successor(f_i);
    f_o = successor(f_o);
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
O my_copy(I f_i, I l_i, O f_o)
{
    // Precondition:
    //     not_overlapped_forward(f_i, l_i, f_o, f_o + (l_i - f_i))
    while (f_i != l_i) my_copy_step(f_i, f_o);
    return f_o;
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
pair<I, O> my_copy_bounded(I f_i, I l_i, O f_o, O l_o)
{
    // Precondition:
    //     not_overlapped_forward(f_i, l_i, f_o, l_o)
    while (f_i != l_i && f_o != l_o) my_copy_step(f_i, f_o);
    return pair<I, O>(f_i, f_o);
}

template<typename N>
    requires(Integer(N))
bool count_down(N& n)
{
    // Precondition: n >= 0
    if (zero(n)) return false;
    n = predecessor(n);
    return true;
}

template<typename I, typename O, typename N>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O) &&
        Integer(N))
pair<I, O> my_copy_n(I f_i, N n, O f_o)
{
    // Precondition:
    //     not_overlapped_forward(f_i, f_i + n, f_o, f_o + n)
    while (count_down(n)) my_copy_step(f_i, f_o);
    return pair<I, O>(f_i, f_o);
}

template<typename I, typename O>
    requires(Readable(I) &&
        BidirectionalIterator(I) &&
        Writable(O) &&
        BidirectionalIterator(O))
void my_copy_backward_step(I& l_i, O& l_o)
{
    // Preconditions:
    //     source(predecessor(l_i)) is defined
    //     sink(predecessor(l_o)) is defined
    l_i = predecessor(l_i);
    l_o = predecessor(l_o);
    sink(l_o) = source(l_i);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
O my_copy_backward(I f_i, I l_i, O l_o)
{
    // Preconditions:
    //     not_overlapped_backward(f_i, l_i, l_o - (l_i - f_i), l_o)
    while (f_i != l_i) my_copy_backward_step(l_i, l_o);
    return l_o;
}

template<typename I, typename N, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        Integer(N) && ValueType(I) == ValueType(O))
pair<I, O> my_copy_backward_n(I l_i, N n, O l_o)
{
    // Preconditions:
    //     not_overlapped_backward(l_i - n, l_i, l_o - n, l_o)
    while (count_down(n)) my_copy_backward_step(l_i, l_o);
    return pair<I, O>(l_i, l_o);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
void my_reverse_copy_step(I& l_i, O& f_o)
{
    // Preconditions:
    //     source(predecessor(l_i)) is defined
    //     sink(f_o) is defined
    l_i = predecessor(l_i);
    sink(f_o) = source(l_i);
    f_o = successor(f_o);
}

template<typename I, typename O>
    requires(Readable(I) && BidirectionalIterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
O my_reverse_copy(I f_i, I l_i, O f_o)
{
    // Preconditions:
    //     not_overlapped_reverse_forward(f_i, l_i, f_o, f_o + (l_i - f_i))
    while (f_i != l_i) my_reverse_copy_step(l_i, f_o);
    return f_o;
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && BidirectionalIterator(O) &&
        ValueType(I) == ValueType(O))
void my_reverse_copy_backward_step(I& f_i, O& l_o)
{
    // Preconditions:
    //     source(f_i) is defined
    //     sink(predecessor(l_o)) is defined
    l_o = predecessor(l_o);
    sink(l_o) = source(f_i);
    f_i = successor(f_i);
}

template<typename I, typename O>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O))
O my_reverse_copy_backward(I f_i, I l_i, O l_o)
{
    // Preconditions:
    //     not_overlapped_reverse_backward(f_i, l_i, l_o - (l_i - f_i), l_o)
    while (f_i != l_i) my_reverse_copy_backward_step(f_i, l_o);
    return l_o;
}

template<typename I, typename O, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O) &&
        UnaryPredicate(P) && I == Domain(P))
O my_copy_select(I f_i, I l_i, O f_t, P p)
{
    // Preconditions:
    //     not_overlapped_forward(f_i, l_i, f_t, f_t + n_t),
    //         where n_t is an upper bound for the number of
    //         iterators in the input range satisfying p
    while (f_i != l_i) {
        if (p(f_i)) my_copy_step(f_i, f_t);
        else f_i = successor(f_i);
    }
    return f_t;
}

template<typename I, typename O, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O) && Iterator(O) &&
        ValueType(I) == ValueType(O) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
O my_copy_if(I f_i, I l_i, O f_t, P p)
{
    // Preconditions:
    //     same as for my_copy_select
    predicate_source<I, P> ps(p);
    return my_copy_select(f_i, l_i, f_t, ps);
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        UnaryPredicate(P) && I == Domain(P))
pair<O_f, O_t> my_split_copy(I f_i, I l_i, O_f f_f, O_t f_t, P p)
{
    // Preconditions:
    //     not_write_overlapped(f_f, n_f, f_t, n_t) ^
    //     ((not_overlapped_forward(f_i, l_i, f_f, f_f + n_f) ^
    //       not_overlapped(f_i, l_i, f_t, l_t)) v
    //      (not_overlapped_forward(f_i, l_i, f_t, f_t + n_t) ^
    //       not_overlapped(f_i, l_i, f_f, l_f)))
    //         where n_f and n_t are the number of iterators
    //         not satisfying and satisfying p, respectively
    while (f_i != l_i)
        if (p(f_i)) my_copy_step(f_i, f_t);
        else        my_copy_step(f_i, f_f);
    return pair<O_f, O_t>(f_f, f_t);
    // Postcondition (Exercise 9.2):
    //     Let f_f, f_t refer to their values at the beginning
    //     of this procedure, and let l_f, l_t refer to their
    //     values at the end of this procedure.  Also, let f_i
    //     refer to its value at the beginning of this procedure.
    //
    //         (1) (l_f - f_f) + (l_t - f_t) = l_i - f_i
    //         (2) Every value in the bounded range f_f, l_f does
    //             not satisfy the predicate
    //         (3) Every value in the bounded range f_t, l_t
    //             satisfies the predicate
    //         (4) The combined set of values of the output ranges
    //             is precisely the set of values of the input range
    //         (5) If an iterator j_o precedes an iterator k_o in one
    //             of the output ranges, then a corresponding
    //             iterator j_i with the same value as j_o precedes
    //             a corresponding iterator k_i with the same value
    //             as k_o in the input range
}

template<typename I, typename O_f, typename O_t, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<O_f, O_t> my_partition_copy(I f_i, I l_i, O_f f_f, O_t f_t, P p)
{
    // Preconditions:
    //     same as my_split_copy
    predicate_source<I, P> ps(p);
    return my_split_copy(f_i, l_i, f_f, f_t, ps);
}

template<typename I, typename O_f, typename O_t, typename N, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        Integer(N) && UnaryPredicate(P) &&
        I == Domain(P))
triple<I, O_f, O_t> my_split_copy_n(I f_i, N n, O_f f_f, O_t f_t, P p)
{
    // Preconditions:
    //     not_write_overlapped(f_f, n_f, f_t, n_t) ^
    //     ((not_overlapped_forward(f_i, f_i + n, f_f, f_f + n_f) ^
    //       not_overlapped(f_i, f_i + n, f_t, l_t)) v
    //      (not_overlapped_forward(f_i, f_i + n, f_t, f_t + n_t) ^
    //       not_overlapped(f_i, f_i + n, f_f, l_f)))
    //         where n_f and n_t are the number of iterators
    //         not satisfying and satisfying p, respectively
    while (count_down(n))
        if (p(f_i)) my_copy_step(f_i, f_t);
        else        my_copy_step(f_i, f_f);
    return triple<I, O_f, O_t>(f_i, f_f, f_t);
}

template<typename I, typename O_f, typename O_t, typename N, typename P>
    requires(Readable(I) && Iterator(I) &&
        Writable(O_f) && Iterator(O_f) &&
        Writable(O_t) && Iterator(O_t) &&
        ValueType(I) == ValueType(O_f) &&
        ValueType(I) == ValueType(O_t) &&
        Integer(N) && UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
triple<I, O_f, O_t> my_partition_copy_n(I f_i, N n, O_f f_f, O_t f_t, P p)
{
    // Preconditions:
    //     same as my_split_copy_n
    predicate_source<I, P> ps(p);
    return my_split_copy_n(f_i, n, f_f, f_t, ps);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 0) && I1 == InputType(R, 1))
O my_combine_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, R r)
{
    // Preconditions:
    //     (backward_offset(f_i0, l_i0, f_o, l_o, l_i1 - f_i1) ^
    //      not_overlapped(f_i1, l_i1, f_o, l_o)) v
    //     (backward_offset(f_i1, l_i1, f_o, l_o, l_i0 - f_i0) ^
    //      not_overlapped(f_i0, l_i0, f_o, l_o))
    //         where l_o = f_o + (l_i0 - f_i0) + (l_i1 - f_i1) is
    //         the limit of the output range
    while (f_i0 != l_i0 && f_i1 != l_i1)
        if (r(f_i1, f_i0)) my_copy_step(f_i1, f_o);
        else               my_copy_step(f_i0, f_o);
    return my_copy(f_i1, l_i1, my_copy(f_i0, l_i0, f_o));
    // Postconditions (Exercise 9.3)
    //     Let f_o refer to the value of the argument at the beginning
    //     of the procedure, and let l_o refer to the returned result.
    //
    //         (1) (l_i0 - f_i0) + (l_i1 - f_i1) = l_o - f_o
    //         (2) The set of values of the output range is precisely
    //             the combined set of values of the input ranges
    //         (3) If an iterator j_i precedes an iterator k_i in one
    //             of the input ranges, then a corresponding
    //             iterator j_o with the same value as j_i precedes
    //             a corresponding iterator k_o with the same value
    //             as k_i in the input range
    //
    // Proof.
    //     (1) Let f_o' be the original value of f_o.  We will show that
    //         (f_o - f_o') + (l_i0 - f_i0) + (l_i1 - f_i1) is invariant
    //         throughout the procedure.  At each iteration of the while
    //         loop, either my_copy_step advances both f_i1 and f_o by
    //         one step (which adds 1 to (f_o - f_o') and subtracts 1 from
    //         (l_i1 - f_i1), preserving the invariant), or advances both
    //         f_i0 and f_o by one step (which adds 1 to (f_o - f_o') and
    //         subtracts 1 from (l_i1 - f_i1), preserving the invariant).
    //         Next, the first call to my_copy will return a value
    //         f_o + (f_i0 - l_i0), and the second call will return a
    //         an iterator l_o = f_o + (l_i0 - f_i0) + (f_i1 - l_i1).
    //         Subtracting f_o' from both sides gives
    //         l_o - f_o' = (f_o - f_o') + (l_i0 - f_i0) + (f_i1 - l_i1),
    //         and the invariant shows that l_o - f_o' is equal to
    //         (f_o' - f_o') + (l_i0 - f_i0) + (f_i1 - l_i1) where
    //         l_i0, f_i0, l_i1, f_i1 refer to their values at the beginning
    //         of the procedure.
    //     (2) Let n be the value of (l_i0 - f_i0) + (l_i1 - f_i1) at the
    //         beginning of the while loop.  We will prove by induction on
    //         n that (2) holds for the subranges of the input and output
    //         defined by the values of l_i0, f_i0, l_i1, f_i1, f_o at the
    //         beginning of the while loop.  If n == 0 then there is nothing
    //         to prove.  Suppose n > 0 and the claim holds for m < n.  If
    //         either (l_i0 - f_i0) or (l_i1 - f_i1) equals 0, then the while loop
    //         will terminate, and our claim follows from the fact that (2)
    //         holds for my_copy.  Otherwise, the procedure makes one call
    //         to my_copy_step and advances f_o as well as f_ib (b = 0 or 1).
    //         Then the value of f_o (before advancing) corresponds to the
    //         value of f_ib (before advancing), and the correspondence
    //         between the updated input ranges (after advancing f_ib) and the
    //         updated output range (after advancing f_o) follows from the
    //         inductive hypothesis.  Since (2) holds for any values of
    //         l_i0, ..., f_o at the beginning of the while loop, and the
    //         while loop is at the beginning of the procedure, we conclude
    //         that (2) holds for the entire procedure.
    //     (3) We again proceed by induction on n (where n is defined as in
    //         (2).  If n == 0 then there is nothing to prove.  Suppose n > 0
    //         and the claim holds for m < n.  If either (l_i0 - f_i0) or
    //         (l_i1 - f_i1) equals 0, then the while loop will terminate,
    //         and our claim follows from the fact that (3) holds for my_copy.
    //         Otherwise, the element that my_copy_step copies from f_ib
    //         (b = 0 or 1) to f_o precedes every other element in the range
    //         defined by f_ib, l_ib, and the inductive hypothesis implies that
    //         the (3) holds for the remaining elements.
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Relation(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == Domain(R))
O my_merge_copy(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O f_o, R r)
{
    // Preconditions:
    //     those of my_combine_copy, plus:
    //     weak_ordering(r)
    //     increasing_range(f_i0, l_i0, r)
    //     increasing_range(f_i1, l_i1, r)
    relation_source<I0, I1, R> rs(r);
    return my_combine_copy(f_i0, l_i0, f_i1, l_i1, f_o, rs);
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 0) && I1 == InputType(R, 1))
O my_combine_copy_backward(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O l_o, R r)
{
    // Preconditions:
    //     (forward_offset(f_i0, l_i0, f_o, l_o, l_i1 - f_i1) ^
    //      not_overlapped(f_i1, l_i1, f_o, l_o)) v
    //     (forward_offset(f_i1, l_i1, f_o, l_o, l_i0 - f_i0) ^
    //      not_overlapped(f_i0, l_i0, f_o, l_o))
    //         where l_o = f_o + (l_i0 - f_i0) + (l_i1 - f_i1) is
    //         the limit of the output range
    while (f_i0 != l_i0 && f_i1 != l_i1) {
        if (r(predecessor(l_i1), predecessor(l_i0)))
            my_copy_backward_step(l_i0, l_o);
        else
            my_copy_backward_step(l_i1, l_o);
    }
    return my_copy_backward(f_i0, l_i0,
                            my_copy_backward(f_i1, l_i1, l_o));
}

template<typename I0, typename I1, typename O, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == InputType(R, 0) &&
        ValueType(I1) == InputType(R, 1))
O my_merge_copy_backward(I0 f_i0, I0 l_i0, I1 f_i1, I1 l_i1, O l_o, R r)
{
    // Preconditions:
    //     those of my_combine_copy_backward, plus:
    //     weak_ordering(r)
    //     increasing_range(f_i0, l_i0, r)
    //     increasing_range(f_i1, l_i1, r)
    relation_source<I0, I1, R> rs(r);
    return my_combine_copy_backward(f_i0, l_i0, f_i1, l_i1, l_o, rs);
}

template<typename I0, typename I1, typename O, typename N, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Integer(N) && BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 0) && I1 == InputType(R, 1))
triple<I0, I1, O> my_combine_copy_n(I0 f_i0, N n0, I1 f_i1, N n1, O f_o, R r)
{
    // Preconditions:
    //     (backward_offset(f_i0, f_i0 + n0, f_o, l_o, n1) ^
    //      not_overlapped(f_i1, f_i1 + n1, f_o, l_o)) v
    //     (backward_offset(f_i1, f_i1 + n1, f_o, l_o, n0) ^
    //      not_overlapped(f_i0, f_i0 + n0, f_o, l_o))
    //         where l_o = f_o + n0 + n1 is
    //         the limit of the output range
    while (!zero(n0) && !zero(n1)) {
        if (r(f_i1, f_i0)) {
            count_down(n1);
            my_copy_step(f_i1, f_o);
        } else {
            count_down(n0);
            my_copy_step(f_i0, f_o);
        }
    }
    pair<I0, O> p0 = my_copy_n(f_i0, n0, f_o);
    pair<I0, O> p1 = my_copy_n(f_i1, n1, p0.second);
    return triple<I0, I1, O>(p0.first, p1.first, p1.second);
}

template<typename I0, typename I1, typename O, typename N, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Integer(N) && Relation(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == Domain(R))
triple<I0, I1, O> my_merge_copy_n(I0 f_i0, N n0, I1 f_i1, N n1, O f_o, R r)
{
    // Preconditions:
    //     those of my_combine_copy, plus:
    //     weak_ordering(r)
    //     increasing_range(f_i0, f_i0 + n0, r)
    //     increasing_range(f_i1, f_i1 + n1, r)
    relation_source<I0, I1, R> rs(r);
    return my_combine_copy_n(f_i0, n0, f_i1, n1, f_o, rs);
}

template<typename I0, typename I1, typename O, typename N, typename R>
    requires(Readable(I0) && BidirectionalIterator(I0) &&
        Readable(I1) && BidirectionalIterator(I1) &&
        Writable(O) && BidirectionalIterator(O) &&
        Integer(N) && BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        I0 == InputType(R, 0) && I1 == InputType(R, 1))
triple<I0, I1, O> my_combine_copy_backward_n(I0 l_i0, N n0, I1 l_i1, N n1, O l_o, R r)
{
    // Preconditions:
    //     (forward_offset(l_i0 - n0, l_i0, f_o, l_o, n1) ^
    //      not_overlapped(l_i1 - n1, l_i1, f_o, l_o)) v
    //     (forward_offset(l_i1 - n1, l_i1, f_o, l_o, n0) ^
    //      not_overlapped(l_i0 - n0, l_i0, f_o, l_o))
    //         where f_o = l_o - n0 - n1 is
    //         the beginning of the output range
    while (!zero(n0) && !zero(n1)) {
        if (r(predecessor(l_i1), predecessor(l_i0))) {
            count_down(n0);
            my_copy_backward_step(l_i0, l_o);
        } else {
            count_down(n1);
            my_copy_backward_step(l_i1, l_o);
        }
    }
    pair<I1, O> p1 = my_copy_backward_n(l_i1, n1, l_o);
    pair<I0, O> p0 = my_copy_backward_n(l_i0, n0, p1.second);
    return triple<I0, I1, O>(p0.first, p1.first, p0.second);
}

template<typename I0, typename I1, typename O, typename N, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        Writable(O) && Iterator(O) &&
        Integer(N) && BinaryPredicate(R) &&
        ValueType(I0) == ValueType(O) &&
        ValueType(I1) == ValueType(O) &&
        ValueType(I0) == InputType(R, 0) &&
        ValueType(I1) == InputType(R, 1))
triple<I0, I1, O> my_merge_copy_backward_n(I0 l_i0, N n0, I1 l_i1, N n1, O l_o, R r)
{
    // Preconditions:
    //     those of my_combine_copy_backward, plus:
    //     weak_ordering(r)
    //     increasing_range(l_i0 - n0, l_i0, r)
    //     increasing_range(l_i1 - n1, l_i1, r)
    relation_source<I0, I1, R> rs(r);
    return my_combine_copy_backward_n(l_i0, n0, l_i1, n1, l_o, rs);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && Mutable(I1) &&
        ValueType(I0) == ValueType(I1))
void exchange_values(I0 x, I1 y)
{
    // Precondition: deref(x) and deref(y) are defined
    ValueType(I0) t = source(x);
            sink(x) = source(y);
            sink(y) = t;
    // Postconditions (Exercise 9.7):
    //   (forall z in ValueType(I0))
    //       z == source(x) before exchange_values was called
    //           implies z == source(y) after exchange_values was called
    //   (forall z in ValueType(I0))
    //       z == source(y) before exchange_values was called
    //           implies z == source(x) after exchange_values was called
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
void my_swap_step(I0& f0, I1& f1)
{
    // Preconditions:
    //     deref(f0) is defined
    //     deref(f1) is defined
    exchange_values(f0, f1);
    f0 = successor(f0);
    f1 = successor(f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
I1 my_swap_ranges(I0 f0, I0 l0, I1 f1)
{
    // Preconditions:
    //     mutable_bounded_range(f0, l0)
    //     mutable_counted_range(f1, l0 - f0)
    while (f0 != l0) my_swap_step(f0, f1);
    return f1;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
pair<I0, I1> my_swap_ranges_bounded(I0 f0, I0 l0, I1 f1, I1 l1)
{
    // Preconditions:
    //     mutable_bounded_range(f0, l0)
    //     mutable_bounded_range(f1, l1)
    while (f0 != l0 && f1 != l1) my_swap_step(f0, f1);
    return pair<I0, I1>(f0, f1);
}

template<typename I0, typename I1, typename N>
    requires(Mutable(I0) && ForwardIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Integer(N))
pair<I0, I1> my_swap_ranges_n(I0 f0, I1 f1, N n)
{
    // Preconditions:
    //     mutable_counted_range(f0, n)
    //     mutable_counted_range(f1, n)
    while (count_down(n)) my_swap_step(f0, f1);
    return pair<I0, I1>(f0, f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
void my_reverse_swap_step(I0& l0, I1& f1)
{
    // Precondtions:
    //     deref(predecessor(l0)) is defined
    //     deref(f1) is defined
    l0 = predecessor(l0);
    exchange_values(l0, f1);
    f1 = successor(f1);
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
I1 my_reverse_swap_ranges(I0 f0, I0 l0, I1 f1)
{
    // Precondtions:
    //     mutable_bounded_range(f0, l0)
    //     mutable_counted_range(f1, l0 - f0)
    while (f0 != l0) my_reverse_swap_step(l0, f1);
    return f1;
}

template<typename I0, typename I1>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1))
pair<I0, I1> my_reverse_swap_ranges_bounded(I0 f0, I0 l0, I1 f1, I1 l1)
{
    // Precondtions:
    //     mutable_bounded_range(f0, l0)
    //     mutable_bounded_range(f1, l0)
    while (f0 != l0 && f1 != l1) my_reverse_swap_step(l0, f1);
    return pair<I0, I1>(l0, f1);
}

template<typename I0, typename I1, typename N>
    requires(Mutable(I0) && BidirectionalIterator(I0) &&
        Mutable(I1) && ForwardIterator(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Integer(N))
pair<I0, I1> my_reverse_swap_ranges_n(I0 l0, I1 f1, N n)
{
    // Precondtions:
    //     mutable_counted_range(l0 - n, n)
    //     mutable_counted_range(f1, n)
    while (count_down(n)) my_reverse_swap_step(l0, f1);
    return pair<I0, I1>(l0, f1);
}

template<typename R, typename T>
    requires(BinaryRelation(R) &&
        Domain(R) == T)
struct counting_relation
{
    R r;
    int& n;
    counting_relation(R r, int& n) : r(r), n(n) {}
    bool operator()(const T& x, const T& y)
    {
        n = successor(n);
        return r(x, y);
    }
};

template<typename T>
void print(T x)
{
    cout << x << endl;
}

pair<link_node<int>*, link_node<int>*>
new_linked_list(int n, int value, int delta)
{
    // Precondition: n > 0 && n * delta <= INT_MAX
    typedef link_node<int> T;
    typedef link_node<int>* I;
    typedef link_node_bidirectional_linker<int> S;
    S set_link;
    I head = new T(value);
    I curr = head;
    n = predecessor(n);
    while (!zero(n)) {
        value = value + delta;
        set_link(curr, new T(value));
        curr = successor(curr);
        n = predecessor(n);
    }
    I end = new T(0);
    set_link(curr, end);
    return pair<I, I>(head, end);
}

int* sorted_random_array(int n, int upper)
{
    int* array = new int[n];
    for (int i = 0; i < n; ++i)
        array[i] = rand() % upper;
    sort(array, array + n);
    return array;
}

double merge_copy_average_comparisons(int n0, int n1, int upper, int trials)
{
    double result = 0.0;
    int count;
    counting_relation<less<int>, int> cr(less<int>(), count);
    for (int i = 0; i < trials; ++i) {
        int* f_i0 = sorted_random_array(n0, upper);
        int* f_i1 = sorted_random_array(n1, upper);
        int* f_o = new int[n0 + n1];
        count = 0;
        my_merge_copy(f_i0, f_i0 + n0, f_i1, f_i1 + n1, f_o, cr);
        result = result + cr.n;
        delete[] f_i0;
        delete[] f_i1;
        delete[] f_o;
    }
    return result / trials;
}

int main() {
    srand(clock());
    rand();

    int n = 10;
    int* x = sorted_random_array(n, 10);
    int* y = sorted_random_array(n, 10);

    copy(x, x + n, ostream_iterator<int>(cout, " ")); cout << endl;
    copy(y, y + n, ostream_iterator<int>(cout, " ")); cout << endl;

    cout << endl;
    my_reverse_swap_ranges_n(x + n, y, 5);

    copy(x, x + n, ostream_iterator<int>(cout, " ")); cout << endl;
    copy(y, y + n, ostream_iterator<int>(cout, " ")); cout << endl;
}
