#include <iostream>
#include "my_copy.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_link.h"
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
    // Preconditions:
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
    // Preconditions:
    //     mutable_bounded_range(f, l)
    predicate_source<I, P> ps(p);
    return potential_partition_point(f, l, ps);
}

template<typename I, typename P>
    requires(Mutable(I) && ForwardIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_partition_semistable(I f, I l, P p)
{
    // Preconditions:
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
    // Preconditions:
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
    // Preconditions:
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
    // Preconditions:
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
    // Preconditions:
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
    // Preconditions:
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
    // Preconditions:
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
    // Preconditions:
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

int main() {
    int n = 20;
    int* x = new_array_list(n, 1, 1);

    /*
    cout << boolalpha << my_partitioned_at_point_source(x, x + n, x + 5, even<int>) << endl;
    cout << boolalpha << my_partitioned_at_point_source(x, x + n, x + 5, bind2nd(greater<int>(), 5)) << endl;
    */

    copy(x, x + n, ostream_iterator<int>(cout, " ")); cout << endl;
    my_partition_bidirectional_single_cycle(x, x + n, even<int>);
    copy(x, x + n, ostream_iterator<int>(cout, " ")); cout << endl;

    delete [] x;
}
