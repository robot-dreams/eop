#include <cassert>
#include <iostream>
#include <set>
#include <vector>
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
    // - there exists some n in DistanceType(F) such that n >= 0 and f^n(x0) = f^n(x1)
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
Domain(F)* convergent_point_guarded(Domain(F) x0, Domain(F) x1, F f, P p)
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

template<typename F, typename P>
    requires(Transformation(F) && UnaryPredicate(P) &&
        Domain(F) == Domain(P))
triple<DistanceType(F), DistanceType(F), Domain(F)>
orbit_structure(const Domain(F)& x, F f, P p)
{
    // Preconditions:
    // p(x) if and only if f(x) is defined
    typedef DistanceType(F) N;
    Domain(F) y = connection_point(x, f, p);
    N m = distance(x, y, f);
    N n(0);
    if (p(y)) n = distance(f(y), y, f);
    // Terminating: m = h - 1, n = 0
    // Otherwise: m = h, n = c - 1
    return triple<N, N, Domain(F)>(m, n, y);
}

template<typename F>
    requires(Transformation(F))
triple<DistanceType(F), DistanceType(F), Domain(F)>
orbit_structure_nonterminating_orbit(const Domain(F)& x, F f)
{
    typedef DistanceType(F) N;
    Domain(F) y = connection_point_nonterminating_orbit(x, f);
    return triple<N, N, Domain(F)>(distance(x, y, f),
                                   distance(f(y), y, f),
                                   y);
}

class Node {
public:
    int value;
    Node* next;

    Node() : value(0), next(NULL), deleting(false) {
    }

    Node(int value, Node* next) : value(value), next(next), deleting(false) {
    }

    ~Node() {
        Node* toDelete = next;
        next = NULL;
        deleting = true;
        if (toDelete != NULL && !toDelete->deleting) delete toDelete;
    }

private:
    bool deleting;
};

template<typename InputIterator>
pair<Node*, Node*> make_linked_list(InputIterator start, InputIterator stop)
{
    Node* head = new Node;
    Node* current = head;
    while (start != stop) {
        current->next = new Node;
        current->next->value = *start;
        current = current->next;
        ++start;
    }
    Node* result = head->next;
    head->next = NULL;
    delete head;
    return make_pair(result, current);
}

template<typename InputIterator>
Node* new_terminating_list(InputIterator start, InputIterator stop)
{
    return make_linked_list(start, stop).first;
}

template<typename InputIterator>
Node* new_circular_list(InputIterator start, InputIterator stop)
{
    pair<Node*, Node*> list = make_linked_list(start, stop);
    list.second->next = list.first;
    return list.first;
}

template<typename InputIterator>
pair<Node*, Node*> make_p_shaped_list(InputIterator handle_start,
                                     InputIterator handle_stop,
                                     InputIterator cycle_start,
                                     InputIterator cycle_stop)
{
    pair<Node*, Node*> handle = make_linked_list(handle_start, handle_stop);
    handle.second->next = new_circular_list(cycle_start, cycle_stop);
    return make_pair(handle.first, handle.second->next);
}

Node* traverse(Node* node)
{
    return node->next;
}

bool can_traverse(Node* node)
{
    return node != NULL;
}

void test_linked_list_cycle_detection() {
    triple<unsigned long, unsigned long, Node*> structure;

    vector<int> v;
    size_t n = 10;
    for (size_t i = 1; i <= n; i++) v.push_back(i);
    Node* terminating = new_terminating_list(v.begin(), v.end());
    structure = orbit_structure(terminating, traverse, can_traverse);
    assert(structure.m0 == n);
    assert(structure.m1 == 0);
    assert(structure.m2 == NULL);
    delete terminating;

    Node* circular = new_circular_list(v.begin(), v.end());
    structure = orbit_structure(circular, traverse, can_traverse);
    assert(structure.m0 == 0);
    assert(structure.m1 == n - 1);
    assert(structure.m2 == circular);
    delete circular;

    pair<Node*, Node*> p_shaped = make_p_shaped_list(v.begin(), v.end(), v.begin(), v.end());
    structure = orbit_structure(p_shaped.first, traverse, can_traverse);
    assert(structure.m0 == n);
    assert(structure.m1 == n - 1);
    assert(structure.m2 == p_shaped.second);
    delete p_shaped.first;

    cout << "Linked list test passed!" << endl;
}

class LcgPredicate {
public:
    LcgPredicate(unsigned long m) : m(m) {
    }

    bool operator()(unsigned long x) {
        return x < m;
    }

private:
    unsigned long m;
};

template<>
struct input_type<LcgPredicate, 0> {
    typedef unsigned long type;
};

class LcgTransformation {
public:
    LcgTransformation(unsigned long a,
                      unsigned long b,
                      unsigned long m) :
        a(a), b(b), m(m) {
    }

    unsigned long operator()(unsigned long x) {
        return (a * x + b) % m;
    }

private:
    unsigned long a;
    unsigned long b;
    unsigned long m;
};

template<>
struct input_type<LcgTransformation, 0> {
    typedef unsigned long type;
};

void test_prng_period_analysis() {
    // https://en.wikipedia.org/wiki/Linear_congruential_generator
    LcgTransformation f(1140671485 , 12820163, 1 << 24);
    LcgPredicate p(1 << 24);
    triple<unsigned long, unsigned long, unsigned long> structure =
        orbit_structure(65535, f, p);

    assert(structure.m0 == 0);
    assert(structure.m1 == (1 << 24) - 1);
    assert(structure.m2 == 65535);

    cout << "PRNG test passed!" << endl;
}

int main() {
    test_linked_list_cycle_detection();
    test_prng_period_analysis();
}
