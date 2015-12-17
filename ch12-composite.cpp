#include <iostream>
#include <string>
#include <unistd.h>
#include <vector>
#include "my_bifurcate.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_rearrangement.h"
#include "my_type_functions.h"
#include "my_underlying.h"

using namespace std;

template<typename T0, typename T1>
    requires(Regular(T0) && Regular(T1))
struct my_pair
{
    T0 m0;
    T1 m1;
    my_pair() {}
    my_pair(const T0& m0, const T1& m1) : m0(m0), m1(m1) {}
};

template<typename T0, typename T1>
    requires(Regular(T0) && Regular(T1))
bool operator==(const my_pair<T0, T1>& x, const my_pair<T0, T1>& y)
{
    return x.m0 == y.m0 && x.m1 == y.m1;
}

template<typename T0, typename T1>
    requires(TotallyOrdered(T0) && TotallyOrdered(T1))
bool operator<(const my_pair<T0, T1>& x, const my_pair<T0, T1>& y)
{
    return x.m0 < y.m0 || (!(y.m0 < x.m0) && x.m1 < y.m1);
}

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
struct array_k
{
    T a[k];
    T& operator[](int i)
    {
        // Precondition: 0 <= i < k
        return a[i];
    };
};

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
T* begin(array_k<k, T>& x)
{
    return &x.a[0];
}

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
T* end(array_k<k, T>& x)
{
    return begin(x) + k;
}

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
bool operator==(array_k<k, T>& x, array_k<k, T>& y)
{
    return my_lexicographical_equal(begin(x), end(x),
                                    begin(y), end(y));
}

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
bool operator<(array_k<k, T>& x, array_k<k, T>& y)
{
    return my_lexicographical_less(begin(x), end(x),
                                   begin(y), end(y));
}

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
int size(const array_k<k, T>& x)
{
    return k;
}

template<int k, typename T>
    requires(k >= 0 && k <= INT_MAX / sizeof(T) &&
        Regular(T))
bool empty(const array_k<k, T>& x)
{
    return k == 0;
}

template<typename I>
    requires(Readable(I) && Iterator(I))
struct bounded_range {
    I f;
    I l;
    bounded_range() {}
    bounded_range(I f, I l) : f(f), l(l) {}
    const ValueType(I)& operator[](DistanceType(I) i)
    {
        // Precondition: 0 <= i < l - f
        return source(f + i);
    }
};

template<typename I>
    requires(Readable(I) && Iterator(I))
I begin(const bounded_range<I>& x) { return x.f; }

template<typename I>
    requires(Readable(I) && Iterator(I))
I end(const bounded_range<I>& x) { return x.l; }

template<typename I>
    requires(Readable(I) && Iterator(I))
DistanceType(I) size(const bounded_range<I>& x)
{
    return end(x) - begin(x);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
bool empty(const bounded_range<I>& x)
{
    return begin(x) == end(x);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
bool operator==(const bounded_range<I>& x,
                const bounded_range<I>& y)
{
    return begin(x) == begin(y) && end(x) == end(y);
}

template<typename I>
    requires(Readable(I) && Iterator(I))
struct my_less< bounded_range<I> >
{
    bool operator()(const bounded_range<I>& x,
                    const bounded_range<I>& y)
    {
        my_less<I> less_I;
        return less_I(begin(x), begin(y)) ||
            (!less_I(begin(y), begin(x)) && less_I(end(x), end(y)));
    }
};

template<typename T0, typename T1>
    requires(Regular(T0), Regular(T1))
struct my_point
{
    T0 m0;
    T1 m1;
    my_point() {}
    my_point(const T0& m0, const T1& m1) : m0(m0), m1(m1) {}
    my_point(const my_point& other)
    {
        cout << "original copy constructor" << endl;
        m0 = other.m0;
        m1 = other.m1;
    }
    my_point& operator=(const my_point& other)
    {
        cout << "original assignment operator" << endl;
        if (this != &other) {
            m0 = other.m0;
            m1 = other.m1;
        }
        return *this;
    }
    ~my_point()
    {
        cout << "original destructor" << endl;
    }
};

template<typename T0, typename T1>
    requires(Regular(T0), Regular(T1))
struct my_underlying_type< my_point<T0, T1> >
{
    typedef my_pair<T0, T1> type;
};

int main()
{
    int n = 5;
    my_point<int, int>* a = new my_point<int, int>[n];
    a[0].m0 = 5;
    a[n - 1].m0 = 1;
    cout << a[0].m0 << endl;
    my_reverse_n_with_temporary_buffer(my_underlying_iterator<my_point<int, int>*>(a), n);
    // my_reverse_n_forward(a, n);
    cout << a[0].m0 << endl;
}
