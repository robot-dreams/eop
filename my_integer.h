#ifndef MY_INTEGER
#define MY_INTEGER

#include "my_intrinsics.h"

template<typename I>
    requires(Integer(I))
inline I successor(I n)
{
    // Preconditions:
    //     n < TypeMax(I)
    return n + 1;
}

template<typename I>
    requires(Integer(I))
inline I predecessor(I n)
{
    // Preconditions:
    //     n > TypeMin(I)
    return n - 1;
}

template<typename I>
    requires(Integer(I))
inline I twice(I n)
{
    // Preconditions:
    //     TypeMin(I) <= 2n <= TypeMax(I)
    return n << 1;
}

template<typename I>
    requires(Integer(I))
inline I half(I n)
{
    // Preconditions:
    //     n >= 0
    return n >> 1;
}

template<typename I>
    requires(Integer(I))
inline I half_nonnegative(I n)
{
    // Preconditions:
    //     n >= 0
    return n >> 1;
}

template<typename I>
    requires(Integer(I))
inline I binary_scale_down_nonnegative(I n, I k)
{
    // Preconditions:
    //     n >= 0
    //     k >= 0
    return n >> k;
}

template<typename I>
    requires(Integer(I))
inline I binary_scale_up_nonnegative(I n, I k)
{
    // Preconditions:
    //     n >= 0
    //     k >= 0
    return n << k;
}

template<typename I>
    requires(Integer(I))
inline bool positive(I n)
{
    return n > 0;
}

template<typename I>
    requires(Integer(I))
inline bool negative(I n)
{
    return n < 0;
}

template<typename I>
    requires(Integer(I))
inline bool zero(I n)
{
    return n == 0;
}

template<typename I>
    requires(Integer(I))
inline bool one(I n)
{
    return n == 1;
}

template<typename I>
    requires(Integer(I))
inline bool even(I n)
{
    return !(n & 1);
}

template<typename I>
    requires(Integer(I))
inline bool odd(I n)
{
    return n & 1;
}

template<typename I>
    requires(Integer(I))
inline I quotient(I a, I b)
{
    return a / b;
}

template<typename I>
    requires(Integer(I))
inline I remainder(I a, I b)
{
    return a % b;
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

#endif
