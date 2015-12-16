#ifndef MY_DIVISION
#define MY_DIVISION

#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename T>
    requires(ArchimedeanMonoid(T))
T remainder_recursive(T a, T b)
{
    // Precondition:
    //     a >= b > 0
    if (a - b >= b) {
        a = remainder_recursive(a, b + b);
        if (a < b) return a;
    }
    return a - b;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T remainder_nonnegative(T a, T b)
{
    // Precondition:
    //     a >= 0 && b > 0
    if (a < b) return a;
    return remainder_recursive(a, b);
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T largest_doubling(T a, T b)
{
    // Precondition:
    //     a >= b > 0
    while (b <= a - b) b = b + b;
    return b;
    // Postcondition:
    //     b <= a < b + b
}

template<typename T>
    requires(HalvableMonoid(T))
T remainder_nonnegative_iterative(T a, T b)
{
    // Precondition:
    //     a >= 0 && b > 0
    if (a < b) return a;
    T c = largest_doubling(a, b);
    a = a - c;
    do {
        c = half(c);
        if (a >= c) a = a - c;
    } while (a >= b);
    return a;
}

template<typename T>
    requires(EuclideanMonoid(T))
T fast_subtractive_gcd(T a, T b)
{
    // Precondition:
    //     a >= 0 && b >= 0 && !(a == 0 && b == 0)
    while (true) {
        if (b == T(0)) return a;
        a = remainder_nonnegative(a, b);
        if (a == T(0)) return b;
        b = remainder_nonnegative(b, a);
    }
}

template<typename T>
    requires(EuclideanMonoid(T))
T gcd(T a, T b)
{
    // Precondition:
    //     a >= 0 && b >= 0 && !(a == 0 && b == 0)
    return fast_subtractive_gcd(a, b);
}

template<typename T>
    requires(ArchimedeanMonoid(T))
pair<QuotientType(T), T> quo_rem_nonnegative(T a, T b)
{
    // Precondition:
    //     a >= 0 && b > 0
    typedef QuotientType(T) N;
    if (a < b) return     pair<N, T>(N(0), a);
    if (a - b < b) return pair<N, T>(N(1), a - b);
    pair<N, T> q = quo_rem_nonnegative(a, b + b);
    N m = twice(q.first);
    a = q.second;
    if (a < b) return pair<N, T>(m, a);
    return            pair<N, T>(successor(m), a - b);
}

template<typename T>
    requires(HalvableMonoid(T))
pair<QuotientType(T), T> quo_rem_nonnegative_iter(T a, T b)
{
    // Precondition:
    //     a >= 0 && b > 0
    typedef QuotientType(T) N;
    if (a < b) return pair<N, T>(N(0), a);
    T c = largest_doubling(a, b);
    a = a - c;
    N n(1);
    while (c != b) {
        n = twice(n);
        c = half(c);
        if (a >= c) {
            a = a - c;
            n = successor(n);
        }
    }
    return pair<N, T>(n, a);
}

template<typename Op>
    requires(BinaryOperation(Op) &&
        ArchimedeanGroup(Domain(Op)))
Domain(Op) remainder(Domain(Op) a, Domain(Op) b, Op rem)
{
    // Precondition:
    //     b != 0
    typedef Domain(Op) T;
    T r;
    if (a < T(0))
        if (b < T(0)) {
            r = -rem(-a, -b);
        } else {
            r = rem(-a, b);
            if (r != T(0)) r = b - r;
        }
        else
            if (b < T(0)) {
                r = rem(a, -b);
                if (r != T(0)) r = b + r;
            } else {
                r = rem(a, b);
            }
    return r;
}

template<typename F>
    requires(HomogeneousFunction(F) && Arity(F) == 2 &&
        ArchimedeanGroup(Domain(F)) &&
        Codomain(F) == pair<QuotientType(Domain(F)),
                            Domain(F)>)
pair<QuotientType(Domain(F)), Domain(F)>
quotient_remainder(Domain(F) a, Domain(F) b, F quo_rem)
{
    // Precondition:
    //     b != 0
    typedef Domain(F) T;
    pair<QuotientType(T), T> q_r;
    if (a < T(0)) {
        if (b < T(0)) {
            q_r = quo_rem(-a, -b); q_r.second = -q_r.second;
        } else {
            q_r = quo_rem(-a, b);
            if (q_r.second != T(0)) {
                q_r.second = b - q_r.second; q_r.first = successor(q_r.first);
            }
            q_r.first = -q_r.first;
        }
    } else {
        if (b < T(0)) {
            q_r = quo_rem(a, -b);
            if (q_r.second != T(0)) {
                q_r.second = b + q_r.second; q_r.first = successor(q_r.first);
            }
            q_r.first = -q_r.first;
        } else
            q_r = quo_rem(a, b);
    }
    return q_r;
}

template<typename T>
    requires(ArchimedeanGroup(T) &&
        HalvableMonoid(T))
pair<QuotientType(T), T>
quotient_remainder(T a, T b)
{
    // Precondition:
    //     b != 0
    return quotient_remainder(a, b, quo_rem_nonnegative_iter<T>);
}

#endif
