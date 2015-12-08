#ifndef MY_POWERS_ACC
#define MY_POWERS_ACC

#include <cassert>
#include "my_intrinsics.h"
#include "my_type_functions.h"
#include "my_integer.h"

template<typename I, typename Acc>
    requires(Integer(I) &&
        LeftBinaryAccumulation(Acc))
void power_left_associated_accumulate_positive_acc(Domain(Acc)& r,
                                                   const Domain(Acc)& a,
                                                   I n,
                                                   Acc acc)
{
    // Preconditions:
    //     positive(n)
    //     addressof(r) != addressof(a)
    assert(&r != &a);
    while (true) {
        acc(r, a);
        if (one(n)) return;
        n = predecessor(n);
    }
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        LeftBinaryAccumulation(Acc))
void power_left_associated_accumulate_acc(Domain(Acc)& r,
                                          const Domain(Acc)& a,
                                          I n,
                                          Acc acc)
{
    // Preconditions:
    //     !negative(n)
    //     addressof(r) != addressof(a)
    assert(&r != &a);
    if (!zero(n))
        power_left_associated_accumulate_positive_acc(r, a, n, acc);
}

template<typename I, typename Acc>
    requires(Integer(I) && LeftBinaryAccumulation(Acc))
void power_left_associated_acc(Domain(Acc)& a, I n, Acc acc)
{
    // Preconditions:
    //     positive(n)
    Domain(Acc) b = a;
    power_left_associated_accumulate_acc(a, b, predecessor(n), acc);
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        LeftBinaryAccumulation(Acc))
void power_left_associated_acc(Domain(Acc)& a,
                               I n,
                               Acc acc,
                               const Domain(Acc)& id)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) a = id;
    else power_left_associated_acc(a, n, acc);
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        RightBinaryAccumulation(Acc))
void power_right_associated_accumulate_positive_acc(Domain(Acc)& r,
                                                    const Domain(Acc)& a,
                                                    I n,
                                                    Acc acc)
{
    // Preconditions:
    //     positive(n)
    //     addressof(r) != addressof(a)
    assert(&r != &a);
    while (true) {
        acc(a, r);
        if (one(n)) return;
        n = predecessor(n);
    }
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        RightBinaryAccumulation(Acc))
void power_right_associated_accumulate_acc(Domain(Acc)& r,
                                           const Domain(Acc)& a,
                                           I n,
                                           Acc acc)
{
    // Preconditions:
    //     !negative(n)
    //     addressof(r) != addressof(a)
    assert(&r != &a);
    if (!zero(n))
        power_right_associated_accumulate_positive_acc(r, a, n, acc);
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        RightBinaryAccumulation(Acc))
void power_right_associated_acc(Domain(Acc)& a, I n, Acc acc)
{
    // Preconditions:
    //     positive(n)
    Domain(Acc) b = a;
    power_right_associated_accumulate_acc(a, b, predecessor(n), acc);
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        RightBinaryAccumulation(Acc))
void power_right_associated_acc(Domain(Acc)& a,
                                I n,
                                Acc acc,
                                const Domain(Acc)& id)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) a = id;
    else power_right_associated_acc(a, n, acc);
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        LeftBinaryAccumulation(Acc))
void power_accumulate_positive_acc(Domain(Acc)& r,
                                   Domain(Acc) a,
                                   I n,
                                   Acc acc)
{
    // Preconditions:
    //     associative(acc)
    //     positive(n)
    while (true) {
        if (odd(n)) {
            acc(r, a);
            if (one(n)) return;
        }
        acc(a, a);
        n = half_nonnegative(n);
    }
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        LeftBinaryAccumulation(Acc))
void power_accumulate_acc(Domain(Acc)& r,
                          Domain(Acc) a,
                          I n,
                          Acc acc)
{
    // Preconditions:
    //     associative(acc)
    //     !negative(n)
    if (!zero(n))
        power_accumulate_positive_acc(r, a, n, acc);
}

template<typename I, typename Acc>
    requires(Integer(I) &&
        LeftBinaryAccumulation(Acc))
void power_acc(Domain(Acc)& a, I n, Acc acc)
{
    // Preconditions:
    //     associative(acc)
    //     positive(n)
    while (even(n)) {
        acc(a, a);
        n = half_nonnegative(n);
        // Since n is even, setting a <- a^2 and n <- n / 2
        // does not change a^n
    }
    // n = 2k + 1 after the loop terminates
    // The next line sets n <- k
    n = half_nonnegative(n);
    // If k = 0, then n = 1; thus a^n = a^1 = a
    if (zero(n)) return;
    // Otherwise, k > 0, and
    //     a^n = a^{2k+1}
    //         = a * a^{2k}
    //         = a * (a^2)^k
    Domain(Acc) b = a;
    acc(b, b);
    power_accumulate_positive_acc(a, b, n, acc);
}

template<typename I, typename Acc>
    requires(Integer(I) && BinaryAccumulation(Acc))
void power_acc(Domain(Acc)& a, I n, Acc acc, const Domain(Acc)& id)
{
    // Preconditions:
    //     associative(acc)
    //     !negative(n)
    if (zero(n)) a = id;
    else power_acc(a, n, acc);
}

#endif
