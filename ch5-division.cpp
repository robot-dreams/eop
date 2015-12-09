#include <cmath>
#include <iostream>
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

int main() {
    cout << gcd_esm<int, int>(5, 0) << endl;
    cout << gcd_esm<int, int>(5, 12592) << endl;
    cout << gcd_esm<int, int>(5055, 1593415) << endl;
    cout << gcd_esm<int, int>(0, 5) << endl;
}
