#include <iostream>
#include <set>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename F>
    requires(Transformation(F))
DistanceType(F) distance(Domain(F) x, Domain(F) y, F f)
{
    // Preconditions:
    // - y is reachable from x under f
    typedef DistanceType(F) N;
    N n = N(0);
    while (x != y) {
        x = f(x);
        n = n + N(1);
    }
    return n;
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
Domain(F) connection_point_naive(Domain(F) x, F f, P p)
{
    set<Domain(F)> seen;
    while (p(x) && seen.find(x) == seen.end()) {
        seen.insert(x);
        x = f(x);
    }
    return x;
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
Domain(F) collision_point(const Domain(F)& x, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    if (!p(x)) return x;

    Domain(F) slow = x;         // slow = f^0(x)
    Domain(F) fast = f(x);      // fast = f^1(x)
                                // n <- 0 (completed iterations)
    while (fast != slow) {      // slow = f^n(x)     ^ fast = f^{2n+1}(x)
        slow = f(slow);         // slow = f^{n+1}(x) ^ fast = f^{2n+3}(x)
        if (!p(fast)) return fast;
        fast = f(fast);         // slow = f^n(x)     ^ fast = f^{2n+2}(x)
        if (!p(fast)) return fast;
        fast = f(fast);         // slow = f^n(x)     ^ fast = f^{2n+3}(x)
                                // n <- n + 1
    }
    return fast;                // slow = f^n(x)     ^ fast = f^{2n+1}(x)
    // Postconditions:
    // - return value is terminal point or collision point
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
bool terminating(const Domain(F)& x, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    return !p(collision_point(x, f, p));
}

template<typename F>
    requires(Transformation(F))
Domain(F)
collision_point_nonterminating_orbit(const Domain(F)& x, F f)
{
    Domain(F) slow = x;         // slow = f^0(x)
    Domain(F) fast = f(x);      // fast = f^1(x)
                                // n <- 0 (completed iterations)
    while (fast != slow) {      // slow = f^n(x)     ^ fast = f^{2n+1}(x)
        slow = f(slow);         // slow = f^{n+1}(x) ^ fast = f^{2n+1}(x)
        fast = f(fast);         // slow = f^{n+1}(x) ^ fast = f^{2n+2}(x)
        fast = f(fast);         // slow = f^{n+1}(x) ^ fast = f^{2n+3}(x)
                                // n <- n + 1
    }
    return fast;                // slow = f^n(x)     ^ fast = f^{2n+1}(x)
    // Postconditions:
    // - return value is collision point
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(F) &&
        Domain(F) == Domain(P))
bool circular(const Domain(F)& x, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    Domain(F) y = collision_point(x, f, p);
    return p(y) && x == f(y);
}

template<typename F>
    requires(Transformation(F))
bool circular_nonterminating_orbit(const Domain(F)& x, F f)
{
    return x == f(collision_point_nonterminating_orbit(x, f));
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P)
        && Domain(F) == Domain(P))
DistanceType(F) cycle_size(const Domain(F)& x, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    typedef DistanceType(F) N;
    Domain(F) y = collision_point(x, f, p);
    if (!p(y)) return N(0);
    return N(1) + distance(f(y), y, f);
}

template<typename F>
    requires(Transformation(F))
DistanceType(F) cycle_size_nonterminating_orbit(const Domain(F)& x, F f)
{
    typedef DistanceType(F) N;
    Domain(F) y = collision_point_nonterminating_orbit(x, f);
    return N(1) + distance(f(y), y, f);
}

template<typename F>
    requires(Transformation(F))
Domain(F) convergent_point(Domain(F) x0, Domain(F) x1, F f)
{
    // Preconditions:
    // - there exists in DistanceType(F) such that n >= 0 and f^n(x0) = f^n(x1)
    while (x0 != x1) {
        x0 = f(x0);
        x1 = f(x1);
    }
    return x0;
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
Domain(F) connection_point(const Domain(F)& x, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    Domain(F) y = collision_point(x, f, p);
    if (!p(y)) return y;
    return convergent_point(x, f(y), f);
}

template<typename F>
    requires(Transformation(F))
Domain(F)
connection_point_nonterminating_orbit(const Domain(F)& x, F f)
{
    return convergent_point(
            x,
            f(collision_point_nonterminating_orbit(x, f)),
            f);
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
bool intersects(const Domain(F)& x0, const Domain(F)& x1, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    Domain(F) y0 = collision_point(x0, f, p);
    Domain(F) y1 = collision_point(x1, f, p);
    if (!p(y0) || !p(y1)) return y0 == y1;

    Domain(F) y = y0;
    do {
        if (y == y1) return true;
        y = f(y);
    } while (y != y0);
    return false;
}

template<typename F>
    requires(Transformation(F))
bool intersects_nonterminating_orbit(const Domain(F)& x0, const Domain(F)& x1, F f)
{
    Domain(F) y0 = collision_point_nonterminating_orbit(x0, f);
    Domain(F) y1 = collision_point_nonterminating_orbit(x1, f);
    Domain(F) y = y0;
    do {
        if (y == y1) return true;
        y = f(y);
    } while (y != y0);
    return false;
}

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
pointer(Domain(F)) convergent_point_guarded(Domain(F) x0, Domain(F) x1, F f, P p)
{
    // Preconditions:
    // - p(x) if and only if f(x) is defined
    // - intersects(x0, x1, f, p)
    Domain(F) y0 = connection_point(x0, f, p);
    Domain(F) y1 = connection_point(x1, f, p);
    bool x0_entered_cycle = false;
    bool x1_entered_cycle = false;

    while (x0 != x1) {
        if (!p(x0) || !p(x1)) return NULL;
        if (x0 == y0) x0_entered_cycle = true;
        if (x1 == y1) x1_entered_cycle = true;
        if (x0_entered_cycle && x1_entered_cycle) return NULL;
        x0 = f(x0);
        x1 = f(x1);
    }
    return new Domain(F)(x0);
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

int main() {
    cout << boolalpha;
    int* result = convergent_point_guarded(3, 2, mod_square<13>, mod_valid<13>);
    if (result != NULL) {
        cout << *result << endl;
    }
}
