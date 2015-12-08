#include <iomanip>
#include <iostream>
#include <string>
#include <unistd.h>
#include "my_intrinsics.h"
#include "my_type_functions.h"
#include "my_integer.h"

using namespace std;

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_left_associated(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     n > 0
    if (n == I(1)) return a;
    return op(power_left_associated(a, n - I(1), op), a);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_right_associated(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     n > 0
    if (n == I(1)) return a;
    return op(a, power_right_associated(a, n - I(1), op));
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_0(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n > 0
    if (n == I(1)) return a;
    if (n % I(2) == I(0))
        return power_0(op(a, a), n / I(2), op);
    return op(power_0(op(a, a), n / I(2), op), a);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_1(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n > 0
    if (n == I(1)) return a;
    Domain(Op) r = power_1(op(a, a), n / I(2), op);
    if (n % I(2) != I(0)) r = op(r, a);
    return r;
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_0(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n >= 0
    if (n == I(0)) return r;
    if (n % I(2) != I(0)) r = op(r, a);
    return power_accumulate_0(r, op(a, a), n / I(2), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_1(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n >= 0
    if (n == I(0)) return r;
    if (n == I(1)) return op(r, a);
    if (n % I(2) != I(0)) r = op(r, a);
    return power_accumulate_1(r, op(a, a), n / I(2), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_2(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n >= 0
    if (n % I(2) != I(0)) {
        r = op(r, a);
        if (n == I(1)) return r;
    } else if (n == I(0)) return r;
    return power_accumulate_2(r, op(a, a), n / I(2), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_3(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n >= 0
    if (n % I(2) != I(0)) {
        r = op(r, a);
        if (n == I(1)) return r;
    } else if (n == I(0)) return r;
    a = op(a, a);
    n = n / I(2);
    return power_accumulate_3(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_4(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n >= 0
    while (true) {
        if (n % I(2) != I(0)) {
            r = op(r, a);
            if (n == I(1)) return r;
        } else if (n == I(0)) return r;
        a = op(a, a);
        n = n / I(2);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_positive_0(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n > 0
    while (true) {
        if (n % I(2) != I(0)) {
            r = op(r, a);
            if (n == I(1)) return r;
        }
        a = op(a, a);
        n = n / I(2);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_5(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n >= 0
    if (n == I(0)) return r;
    return power_accumulate_positive_0(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_2(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n > 0
    return power_accumulate_5(a, a, n - I(1), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_3(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     n > 0
    while (n % I(2) == I(0)) {
        a = op(a, a);
        n = n / I(2);
        // Since n is even, setting a <- a^2 and n <- n / 2
        // does not change a^n
    }
    // n = 2k + 1 after the loop terminates
    // The next line sets n <- k
    n = n / I(2);
    // If k = 0, then n = 1; thus a^n = a^1 = a
    if (n == I(0)) return a;
    // Otherwise, k > 0, and
    //     a^n = a^{2k+1}
    //         = a * a^{2k}
    //         = a * (a^2)^k
    return power_accumulate_positive_0(a, op(a, a), n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate_positive(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     positive(n)
    while (true) {
        if (odd(n)) {
            r = op(r, a);
            if (one(n)) return r;
        }
        a = op(a, a);
        n = half_nonnegative(n);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_accumulate(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     !negative(n)
    if (zero(n)) return r;
    return power_accumulate_positive(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     associative(op)
    //     positive(n)
    while (even(n)) {
        a = op(a, a);
        n = half_nonnegative(n);
        // Since n is even, setting a <- a^2 and n <- n / 2
        // does not change a^n
    }
    // n = 2k + 1 after the loop terminates
    // The next line sets n <- k
    n = half_nonnegative(n);
    // If k = 0, then n = 1; thus a^n = a^1 = a
    if (zero(n)) return a;
    // Otherwise, k > 0, and
    //     a^n = a^{2k+1}
    //         = a * a^{2k}
    //         = a * (a^2)^k
    return power_accumulate_positive(a, op(a, a), n, op);
}

int addition(int a, int b) {
    return a + b;
}

int multiplication(int a, int b) {
    return a * b;
}

template<int modulus>
int mod_multiply(int a, int b) {
    return static_cast<int>((static_cast<long>(a) * b) % modulus);
}

int subtraction(int a, int b) {
    return a - b;
}

string list(string lhs, string rhs) {
    return string("(") + lhs + string(" ") + rhs + string(")");
}

void test(int (*f)(int, long, int (*)(int, int)), string name) {
    clock_t start, end;
    int result;
    start = clock();
    result = f(2, LONG_MAX, mod_multiply<19599399173>);
    end = clock();
    cout << setw(25) << name << ": " << result << ", ";
    cout << "clock ticks: " << (end - start) << endl;
}

void test_accumulate(int (*f)(int, int, long, int (*)(int, int)), string name) {
    clock_t start, end;
    int result;
    start = clock();
    result = f(1, 2, LONG_MAX, mod_multiply<19599399173>);
    end = clock();
    cout << setw(25) << name << ": " << result << ", ";
    cout << "clock ticks: " << (end - start) << endl;
}

int main() {
    test(power_0, "power_0");
    test(power_1, "power_1");
    test_accumulate(power_accumulate_0, "power_accumulate_0");
    test_accumulate(power_accumulate_1, "power_accumulate_1");
    test_accumulate(power_accumulate_2, "power_accumulate_2");
    test_accumulate(power_accumulate_3, "power_accumulate_3");
    test_accumulate(power_accumulate_4, "power_accumulate_4");
    test_accumulate(power_accumulate_5, "power_accumulate_5");
    test(power_2, "power_2");
    test(power_3, "power_3");
    test(power, "power");
}

