#include <iostream>
#include <set>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

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

template<int modulus>
int mod_increment(int x)
{
    return (x + 1) % modulus;
}

template<int modulus>
bool mod_valid(int x)
{
    return x >= 0 && x < modulus;
}

int main() {
    cout << collision_point(0, mod_increment<13>, mod_valid<13>) << endl;
    cout << collision_point_nonterminating_orbit(0, mod_increment<13>) << endl;
}
