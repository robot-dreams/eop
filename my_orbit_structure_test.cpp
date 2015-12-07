#include <cassert>
#include <iostream>
#include <set>
#include <vector>
#include "my_orbit_structure.h"

using namespace std;

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
