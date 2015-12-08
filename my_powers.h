#ifndef MY_POWERS
#define MY_POWERS

#include "my_intrinsics.h"
#include "my_type_functions.h"
#include "my_integer.h"

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_left_associated_accumulate_positive(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     positive(n)
    while (true) {
        r = op(r, a);
        if (one(n)) return r;
        n = predecessor(n);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_left_associated_accumulate(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) return r;
    return power_left_associated_accumulate_positive(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_left_associated(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     positive(n)
    return power_left_associated_accumulate(a, a, predecessor(n), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_left_associated(Domain(Op) a, I n, Op op, Domain(Op) id)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) return id;
    return power_left_associated(a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_right_associated_accumulate_positive(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     positive(n)
    while (true) {
        r = op(a, r);
        if (one(n)) return r;
        n = predecessor(n);
    }
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_right_associated_accumulate(Domain(Op) r, Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) return r;
    return power_right_associated_accumulate_positive(r, a, n, op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_right_associated(Domain(Op) a, I n, Op op)
{
    // Preconditions:
    //     positive(n)
    return power_right_associated_accumulate(a, a, predecessor(n), op);
}

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power_right_associated(Domain(Op) a, I n, Op op, Domain(Op) id)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) return id;
    return power_right_associated(a, n, op);
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

template<typename I, typename Op>
    requires(Integer(I) && BinaryOperation(Op))
Domain(Op) power(Domain(Op) a, I n, Op op, Domain(Op) id)
{
    // Preconditions:
    //     associative(op)
    //     !negative(n)
    if (zero(n)) return id;
    return power(a, n, op);
}

#endif
