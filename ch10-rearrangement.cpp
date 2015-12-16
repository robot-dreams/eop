#include <cassert>
#include <iostream>
#include "my_copy.h"
#include "my_division.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_rearrangement.h"
#include "my_type_functions.h"
#include "my_test_util.h"

using namespace std;

//
// Begin Exercise 10.3
/////

template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) &&
        I == Domain(F))
void my_cycle_to_2(I i, F f)
{
    // Preconditions:
    //     the orbit of i under f is circular
    //     for all n in N, deref(f^i(n)) is defined
    I k = f(i);
    ValueType(I) tmp;
// in state s0, tmp is available as scratch space and
// source(i) is the value that should be assigned to
// sink(k)
s0:
    if (k == i) return;
    tmp = source(k);
    sink(k) = source(i);
    k = f(k);
    goto s1;
// in state s1, sink(i) is available as scratch space
// and tmp is the value that should be assigned to
// sink(k)
s1:
    if (k == i) { sink(k) = tmp; return; }
    sink(i) = source(k);
    sink(k) = tmp;
    k = f(k);
    goto s0;
}

template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) &&
        I == Domain(F))
void my_cycle_to_3(I i, F f)
{
    // Preconditions:
    //     the orbit of i under f is circular
    //     for all n in N, deref(f^i(n)) is defined
    I k = f(i);
    ValueType(I) buffer;
    ValueType(I)* scratch = &buffer;
    ValueType(I)* next = &sink(i);
    while (k != i) {
        *scratch = source(k);
        sink(k) = *next;
        swap(scratch, next);
        k = f(k);
    }
    if (next != &sink(k)) sink(k) = *next;
}

//
// End Exercise 10.3
/////

template<typename I>
    requires(Mutable(I) && ForwardIterator(I))
I rotate_forward_nontrivial_2(I f, I m, I l)
{
    // Preconditions:
    //     mutable_bounded_range(f, l)
    //     f precedes m, m precedes l
    bool locked = false;
    I m_prime = m;
    while (true) {
        pair<I, I> p = my_swap_ranges_bounded(f, m, m, l);
        if (m == p.first && l == p.second) {
            if (locked) return m_prime;
            else        return m;
        } else if (m == p.first) {
            f = m;
            m = p.second;
        } else {
            if (!locked) {
                m_prime = p.first;
                locked = true;
            }
            f = p.first;
        }
    }
    return m_prime;
}

template<typename I, typename F>
    requires(Mutable(I) && Transformation(F) &&
        I == Domain(F))
void my_cycle_from_2(I i, F f)
{
    // Preconditions:
    //     the orbit of i under f is circular
    //     for all n in N, deref(f^i(n)) is defined
    I j = i;
    I k = f(i);
    while (k != i) {
        exchange_values(j, k);
        j = k;
        k = f(k);
    }
}

template<typename I, typename N>
    requires(ForwardIterator(I) &&
        Integer(N))
struct cycler
{
    I f;
    I l;
    N n;
    cycler(I f, I l, N n) : f(f), l(l), n(n) {}
    I operator()(I i)
    {
        // Precondition: i is in the bounded range
        //     defined by f and l
        N m(n);
        while (count_down(m)) {
            i = successor(i);
            if (i == l) i = f;
        }
        return i;
    }
};

template<typename I, typename N>
    requires(IndexedIterator(I) &&
        Integer(N))
struct adjacent_rotator
{
    I f;
    N n;
    N c;
    adjacent_rotator(I f, N n, N c) : f(f), n(n % c), c(c) {}
    I operator()(I i)
    {
        // Precondition:
        //     counted_range(f, (i - f) - (i - f) % c + c)
        N k = i - f;
        N r = k % c;
        k = k - r;
        r = (r + n) % c;
        k = k + r;
        return f + k;
    }
};

void print(int x)
{
    cout << x << " ";
}

int main()
{
    int n = 10;
    int* x = new_array_list(n, 1, 1);
    copy(x, x + n, ostream_iterator<int>(cout, " "));
    cout << endl;
    my_cycle_to_3(x, adjacent_rotator<int*, int>(x, 2, 5));
    copy(x, x + n, ostream_iterator<int>(cout, " "));
    cout << endl;
    delete[] x;
}
