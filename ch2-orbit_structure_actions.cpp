#include <iostream>
#include <set>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename A>
    requires(Action(A))
DistanceType(A) distance(Domain(A) x, Domain(A) y, A a)
{
    // Preconditions:
    // - y is reachable from x under f
    typedef DistanceType(A) N;
    N n = N(0);
    while (x != y) {
        a(x);
        n = n + N(1);
    }
    return n;
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
Domain(A) connection_point_naive(Domain(A) x, A a, P p)
{
    set<Domain(A)> seen;
    while (p(x) && seen.find(x) == seen.end()) {
        seen.insert(x);
        a(x);
    }
    return x;
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
Domain(A) collision_point(const Domain(A)& x, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if a(x) is defined
    if (!p(x)) return x;

    Domain(A) slow = x;         // slow = f^0(x)
    Domain(A) fast = x;         // fast = f^0(x)
    a(fast);                    // fast = f^1(x)
                                // n <- 0 (completed iterations)
    while (fast != slow) {      // slow = f^n(x)     ^ fast = f^{2n+1}(x)
        a(slow);                // slow = f^{n+1}(x) ^ fast = f^{2n+3}(x)
        if (!p(fast)) return fast;
        a(fast);                // slow = f^n(x)     ^ fast = f^{2n+2}(x)
        if (!p(fast)) return fast;
        a(fast);                // slow = f^n(x)     ^ fast = f^{2n+3}(x)
                                // n <- n + 1
    }
    return fast;                // slow = f^n(x)     ^ fast = f^{2n+1}(x)
    // Postconditions:
    // - return value is terminal point or collision point
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
bool terminating(const Domain(A)& x, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if a(x) is defined
    return !p(collision_point(x, a, p));
}

template<typename A>
    requires(Action(A))
Domain(A)
collision_point_nonterminating_orbit(const Domain(A)& x, A a)
{
    Domain(A) slow = x;         // slow = f^0(x)
    Domain(A) fast = x;         // fast = f^0(x)
    a(fast);                    // fast = f^1(x)
                                // n <- 0 (completed iterations)
    while (fast != slow) {      // slow = f^n(x)     ^ fast = f^{2n+1}(x)
        a(slow);                // slow = f^{n+1}(x) ^ fast = f^{2n+1}(x)
        a(fast);                // slow = f^{n+1}(x) ^ fast = f^{2n+2}(x)
        a(fast);                // slow = f^{n+1}(x) ^ fast = f^{2n+3}(x)
                                // n <- n + 1
    }
    return fast;                // slow = f^n(x)     ^ fast = f^{2n+1}(x)
    // Postconditions:
    // - return value is collision point
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
bool circular(const Domain(A)& x, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    Domain(A) y = collision_point(x, a, p);
    if (!p(y)) return false;
    a(y);
    return x == y;
}

template<typename A>
    requires(Action(A))
bool circular_nonterminating_orbit(const Domain(A)& x, A a)
{
    Domain(A) y = collision_point_nonterminating_orbit(x, a);
    a(y);
    return x == y;
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P)
        && Domain(A) == Domain(P))
DistanceType(A) cycle_size(const Domain(A)& x, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    typedef DistanceType(A) N;
    Domain(A) y = collision_point(x, a, p);
    if (!p(y)) return N(0);
    Domain(A) z = y;
    a(z);
    return N(1) + distance(z, y, a);
}

template<typename A>
    requires(Action(A))
DistanceType(A) cycle_size_nonterminating_orbit(const Domain(A)& x, A a)
{
    typedef DistanceType(A) N;
    Domain(A) y = collision_point_nonterminating_orbit(x, a);
    Domain(A) z = y;
    a(z);
    return N(1) + distance(z, y, a);
}

template<typename A>
    requires(Action(A))
Domain(A) convergent_point(Domain(A) x0, Domain(A) x1, A a)
{
    // Preconditions:
    // - there exists some n in DistanceType(A) such that n >= 0 and f^n(x0) = f^n(x1)
    while (x0 != x1) {
        a(x0);
        a(x1);
    }
    return x0;
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
Domain(A) connection_point(const Domain(A)& x, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    Domain(A) y = collision_point(x, a, p);
    if (!p(y)) return y;
    a(y);
    return convergent_point(x, y, a);
}

template<typename A>
    requires(Action(A))
Domain(A)
connection_point_nonterminating_orbit(const Domain(A)& x, A a)
{
    Domain(A) y = collision_point_nonterminating_orbit(x, a);
    a(y);
    return convergent_point(x, y, a);
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
bool intersects(const Domain(A)& x0, const Domain(A)& x1, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    Domain(A) y0 = collision_point(x0, a, p);
    Domain(A) y1 = collision_point(x1, a, p);
    if (!p(y0) || !p(y1)) return y0 == y1;

    Domain(A) y = y0;
    do {
        if (y == y1) return true;
        a(y);
    } while (y != y0);
    return false;
}

template<typename A>
    requires(Action(A))
bool intersects_nonterminating_orbit(const Domain(A)& x0, const Domain(A)& x1, A a)
{
    Domain(A) y0 = collision_point_nonterminating_orbit(x0, a);
    Domain(A) y1 = collision_point_nonterminating_orbit(x1, a);
    Domain(A) y = y0;
    do {
        if (y == y1) return true;
        a(y);
    } while (y != y0);
    return false;
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
Domain(A)* convergent_point_guarded(Domain(A) x0, Domain(A) x1, A a, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    // - intersects(x0, x1, f, p)
    Domain(A) y0 = connection_point(x0, a, p);
    Domain(A) y1 = connection_point(x1, a, p);
    bool x0_entered_cycle = false;
    bool x1_entered_cycle = false;

    while (x0 != x1) {
        if (!p(x0) || !p(x1)) return NULL;
        if (x0 == y0) x0_entered_cycle = true;
        if (x1 == y1) x1_entered_cycle = true;
        if (x0_entered_cycle && x1_entered_cycle) return NULL;
        a(x0);
        a(x1);
    }
    return new Domain(A)(x0);
}

template<typename A, typename P>
    requires(Action(A) && UnaryPredicate(P) &&
        Domain(A) == Domain(P))
triple<DistanceType(A), DistanceType(A), Domain(A)>
orbit_structure(const Domain(A)& x, A a, P p)
{
    // Preconditions:
    // p(x) if and only if f(x) is defined
    typedef DistanceType(A) N;
    Domain(A) y = connection_point(x, a, p);
    N m = distance(x, y, a);
    N n(0);
    Domain(A) z = y;
    a(z);
    if (p(y)) n = distance(z, y, a);
    // Terminating: m = h - 1, n = 0
    // Otherwise: m = h, n = c - 1
    return triple<N, N, Domain(A)>(m, n, y);
}

template<typename A>
    requires(Action(A))
triple<DistanceType(A), DistanceType(A), Domain(A)>
orbit_structure_nonterminating_orbit(const Domain(A)& x, A a)
{
    typedef DistanceType(A) N;
    Domain(A) y = connection_point_nonterminating_orbit(x, a);
    Domain(A) z = y;
    a(z);
    return triple<N, N, Domain(A)>(distance(x, y, a),
                                   distance(z, y, a),
                                   y);
}

template<int modulus>
int mod_increment(int x)
{
    return (x + 1) % modulus;
}

template<int modulus>
int mod_square(int x)
{
    return (x * x) % modulus;
}

template<int modulus>
bool mod_valid(int x)
{
    return x >= 0 && x < modulus;
}

bool rand_valid(unsigned long x)
{
    return x < (1L << 32);
}

void rand_next(unsigned long& x)
{
    x = (69069L * x + 1L) % (1L << 32);
}

int main() {
    cout << orbit_structure(65535, rand_next, rand_valid) << endl;
}
