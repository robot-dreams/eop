#include <iostream>
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_link.h"
#include "my_type_functions.h"
#include "my_test_util.h"

using namespace std;

template<typename I, typename P>
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) &&
        I == Domain(P))
bool my_partitioned_at_point(I f, I l, I i, P p)
{
    // Preconditions:
    //     bounded_range(f, l)
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
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
bool my_partitioned_at_point_source(I f, I l, I i, P p)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     i in [f, l)
    predicate_source<I, P> ps(p);
    return my_partitioned_at_point(f, l, i, ps);
}

template<typename I, typename P>
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) &&
        I == Domain(P))
I potential_partition_point(I f, I l, P p)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     i in [f, l)
    I i = f;
    while (f != l) {
        if (!p(f)) i = successor(i);
        f = successor(f);
    }
    return i;
}

template<typename I, typename P>
    requires(ForwardIterator(I) &&
        UnaryPredicate(P) &&
        ValueType(I) == Domain(P))
I potential_partition_point_source(I f, I l, P p)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     i in [f, l)
    predicate_source<I, P> ps(p);
    return potential_partition_point(f, l, ps);
}

int main() {
    int n = 10;
    int* x = new_array_list(n, 1, 1);
    cout << potential_partition_point_source(x, x + n, even<int>) - x << endl;
    cout << potential_partition_point_source(x, x + n, bind2nd(greater<int>(), 7)) - x << endl;
    delete [] x;
}
