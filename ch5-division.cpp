#include <cmath>
#include <iostream>
#include "my_division.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename T>
    requires(CancellableMonoid(T))
T slow_remainder(T a, T b)
{
    // Precondition:
    //     a >= 0 ^ b > 0
                            // a0 =  a
                            // n  =  0
    while (b <= a) {        // a  =  a0 - n * b
        a = a - b;          // a  =  a0 - (n + 1) * b
                            // n  =  n + 1
    }
    return a;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
QuotientType(T) slow_quotient(T a, T b)
{
    // Precondition:
    //     a >= 0 ^ b > 0
                            // a0 =  a
    QuotientType(T) n(0);
    while (b <= a) {        // a  =  a0 - n * b
        a = a - b;          // a  =  a0 - (n + 1) * b
        n = successor(n);
    }
    return n;
}

template<typename T>
    requires(ArchimedeanMonoid(T))
T subtractive_gcd_nonzero(T a, T b)
{
    // Precondition:
    //     a > 0 && b > 0
    while (true) {
        if (a > b)      a = a - b; // gcd(a, b) = gcd(a - b, b)
        else if (b > a) b = b - a; // gcd(b, a) = gcd(a, b - a)
        else            return a;  // gcd(a, a) = a
    }
}

template<typename T>
    requires(EuclideanMonoid(T))
T subtractive_gcd(T a, T b)
{
    // Precondition:
    //     a >= 0 && b >= 0 && !(a == 0 && b == 0)
    while (true) {
        if (b == T(0)) return a;
        while (b <= a) a = a - b;
        if (a == T(0)) return b;
        while (a <= b) b = b - a;
    }
}

template<typename T>
    requires(EuclideanSemiring(T))
T gcd_esr(T a, T b)
{
    // Precondition:
    //     !(a == 0 && b == 0)
    while (true) {
        if (b == T(0)) return a;
        a = remainder(a, b);
        if (a == T(0)) return b;
        b = remainder(b, a);
    }
}

template<typename T, typename S>
    requires(EuclideanSemimodule(T, S))
T gcd_esm(T a, T b)
{
    // Precondition:
    //     !(a == 0 && b == 0)
    while (true) {
        if (b == T(0)) return a;
        a = remainder(a, b);
        if (a == T(0)) return b;
        b = remainder(b, a);
    }
}

template<typename T>
    requires(HalvableMonoid(T))
pair<QuotientType(T), T> largest_doubling_2(T a, T b)
{
    // Precondition:
    //     a >= b > 0
    typedef QuotientType(T) N;
    N n(1);
    while (b <= a - b) {
        n = n + n;
        b = b + b;
    }
    return pair<N, T>(n, b);
    // Postcondition:
    //     b <= a < b + b
}

template<typename T>
    requires(HalvableMonoid(T))
pair<QuotientType(T), T> quo_rem_nonnegative_iter_2(T a, T b)
{
    // Precondition:
    //     a >= 0 && b > 0
    typedef QuotientType(T) N;
    if (a < b) return pair<N, T>(N(0), a);
    pair<N, T> p = largest_doubling_2<T>(a, b);
    N m = p.first;
    T c = p.second;
    N n = m;
    a = a - c;
    do {
        m = half(m);
        c = half(c);
        if (a >= c) {
            n = n + m;
            a = a - c;
        }
    } while (a >= b);
    return pair<N, T>(n, a);
}

template<typename Op>
    requires(BinaryOperation(Op) &&
        ArchimedeanGroup(Domain(Op)))
Domain(Op) remainder_2(Domain(Op) a, Domain(Op) b, Op rem)
{
    // Precondition:
    //     b != 0
    typedef Domain(Op) T;
    if (b < T(0)) b = -b;
    if (a < 0) {
        T c = largest_doubling(-a, b);
        a = a + c;
        a = a + c;
    }
    return rem(a, b);
}

template<typename F>
    requires(HomogeneousFunction(F) && Arity(F) == 2 &&
        ArchimedeanGroup(Domain(F)) &&
        Codomain(F) == pair<QuotientType(Domain(F)),
                            Domain(F)>)
pair<QuotientType(Domain(F)), Domain(F)>
quotient_remainder_2(Domain(F) a, Domain(F) b, F quo_rem)
{
    // Preconditions:
    //     b != 0
    //     quo_rem makes Domain(F) an Archimedean monoid
    typedef Domain(F) T;
    typedef QuotientType(T) N;
    pair<N, T> q_r;
    if (a < T(0))
        if (b < T(0)) {
            q_r = quo_rem(-a, -b);
            q_r.second = -q_r.second;
        } else {
            q_r = quo_rem(-a, b);
            q_r.first = -q_r.first;
            if (q_r.second != T(0)) {
                q_r.first = predecessor(q_r.first);
                q_r.second = b - q_r.second;
            }
        }
    else
        if (b < T(0)) {
            q_r = quo_rem(a, -b);
            q_r.first = -q_r.first;
            if (q_r.second != T(0)) {
                q_r.first = predecessor(q_r.first);
                q_r.second = b + q_r.second;
            }
        } else {
            q_r = quo_rem(a, b);
        }
    return q_r;
}

int main() {

}
