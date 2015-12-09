#include <iostream>
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename I>
    requires(Integer(I))
I stein_gcd_positive_0(I a, I b)
{
    // Precondition:
    //     a > 0 && b > 0
    if (a == b)
        return a;
    if (one(a) || one(b))
        return I(1);
    if (a < b)
        return stein_gcd_positive_0(b, a);

    bool a_even = even(a);
    bool b_even = even(b);

    if (a_even && b_even)
        return twice(stein_gcd_positive_0(half(a), half(b)));
    if (a_even && !b_even)
        return stein_gcd_positive_0(half(a), b);
    if (!a_even && b_even)
        return stein_gcd_positive_0(a, half(b));
    else
        return stein_gcd_positive_0(a, half(a - b));
}

// To show that stein_gcd_positive_1 terminates, simply note
// that in every iteration of the loop, at least one of a or b
// decreases by at least 1.  Since a and b never become negative
// or zero (we only call 'half' on even positive integers, and
// we only subtract b from a when we know that a > b), after at
// most a0 + b0 iterations the expression one(a) || one(b) must
// return true

template<typename I>
    requires(Integer(I))
I stein_gcd_positive_1(I a, I b)
{
    // Precondition:
    //     a > 0 && b > 0
    I r = I(1);
    while (true) {
        if (one(a) || one(b)) return r;
        if (a == b) return a * r;
        if (a < b) swap(a, b);
        if (even(a)) {
            if (even(b)) {
                a = half(a);
                b = half(b);
                r = twice(r);
            } else a = half(a);
        } else {
            if (even(b)) b = half(b);
            else         a = half(a - b);
        }
    }
}

template<typename I>
    requires(Integer(I))
I stein_gcd(I a, I b)
{
    // Precondition:
    //     !(a == 0 && b == 0)
    if (zero(a)) return b;
    if (zero(b)) return a;
    if (negative(a)) a = abs(a);
    if (negative(b)) b = abs(b);
    return stein_gcd_positive_1(a, b);
}

int main()
{
    cout << stein_gcd_positive_1(6, 4) << endl;
    cout << stein_gcd_positive_1(656, 44) << endl;
    cout << stein_gcd_positive_1(12 * 12, 24 * 96) << endl;
    cout << stein_gcd_positive_1(111 * 111, 81) << endl;
}
