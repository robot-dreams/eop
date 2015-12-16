#include <cassert>
#include <iostream>
#include "my_bifurcate.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_orbit_structure.h"
#include "my_type_functions.h"

using namespace std;

//
// Exercise 7.2
/////

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
WeightType(C) weight_in(C c)
{
    // Precondition: tree(x)
    typedef WeightType(C) N;
    if (empty(c)) return N(0);
    N n(0);
    C root = c;
    visit v = pre;
    do {
        traverse_step(v, c);
        if (v == in) n = successor(n);
    } while (c != root || v != post);
    return n;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
WeightType(C) weight_post(C c)
{
    // Precondition: tree(x)
    typedef WeightType(C) N;
    if (empty(c)) return N(0);
    N n(0);
    C root = c;
    visit v = pre;
    do {
        traverse_step(v, c);
        if (v == post) n = successor(n);
    } while (c != root || v != post);
    return n;
}

//
// End Exercise 7.2
/////

template<typename C0, typename C1, typename R>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1) &&
        Relation(R) && ValueType(C0) == Domain(R))
bool my_bifurcate_compare_nonempty(C0 c0, C1 c1, R r, visit order)
{
    bool l0, l1, r0, r1;
    switch(order) {
    case pre:
        if (r(source(c0), source(c1))) return true;
        if (r(source(c1), source(c0))) return false;
        if (!has_left_successor(c1)) return false;
        if (!has_left_successor(c0)) return true;
        if (my_bifurcate_compare_nonempty(left_successor(c0), left_successor(c1), r, order)) return true;
        if (my_bifurcate_compare_nonempty(left_successor(c1), left_successor(c0), r, order)) return false;
        if (!has_right_successor(c1)) return false;
        if (!has_right_successor(c0)) return true;
        if (my_bifurcate_compare_nonempty(right_successor(c0), right_successor(c1), r, order)) return true;
        return false;
    case in:
        l0 = has_left_successor(c0);
        l1 = has_left_successor(c1);
        if (l0 && !l1) return false;
        if (!l0 && l1) return true;
        if (l0 && l1) {
            if (my_bifurcate_compare_nonempty(left_successor(c0), left_successor(c1), r, order)) return true;
            if (my_bifurcate_compare_nonempty(left_successor(c1), left_successor(c0), r, order)) return false;
        }
        if (r(source(c0), source(c1))) return true;
        if (r(source(c1), source(c0))) return false;
        if (!has_right_successor(c1)) return false;
        if (!has_right_successor(c0)) return true;
        if (my_bifurcate_compare_nonempty(right_successor(c0), right_successor(c1), r, order)) return true;
        return false;
    case post:
        l0 = has_left_successor(c0);
        l1 = has_left_successor(c1);
        if (l0 && !l1) return false;
        if (!l0 && l1) return true;
        if (l0 && l1) {
            if (my_bifurcate_compare_nonempty(left_successor(c0), left_successor(c1), r, order)) return true;
            if (my_bifurcate_compare_nonempty(left_successor(c1), left_successor(c0), r, order)) return false;
        }
        r0 = has_right_successor(c0);
        r1 = has_right_successor(c1);
        if (r0 && !r1) return false;
        if (!r0 && r1) return true;
        if (r0 && r1) {
            if (my_bifurcate_compare_nonempty(right_successor(c0), right_successor(c1), r, order)) return true;
            if (my_bifurcate_compare_nonempty(right_successor(c1), right_successor(c0), r, order)) return false;
        }
        if (r(source(c0), source(c1))) return true;
        return false;
    }
}

template<typename C0, typename C1, typename R>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1) &&
        Relation(R) && ValueType(C0) == Domain(R))
bool my_bifurcate_compare_nonempty(C0 c0, C1 c1, R r)
{
    return my_bifurcate_compare_nonempty(c0, c1, r, pre);
}

template<typename C0, typename C1>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1))
bool my_bifurcate_less_nonempty(C0 c0, C1 c1)
{
    return my_bifurcate_compare_nonempty(c0, c1, less< ValueType(C0) >());
}

template<typename C, typename Proc>
    requires(BidirectionalBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(P) == 2 &&
        InputType(P, 0) == visit &&
        InputType(P, 1) == C)
Proc aborting_traverse(C c, Proc proc)
{
    // Precondition: tree(c)
    if (empty(c)) return proc;
    C root = c;
    visit v = pre;
    if (proc(pre, c)) return proc;
    do {
        traverse_step(v, c);
        if (proc(v, c)) return proc;
    } while (c != root || v != post);
    return proc;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
class reachable_proc
{
public:
    reachable_proc(C y) : y(y), reachable(false) {}
    bool operator()(visit v, C x)
    {
        if (v == pre) {
            cout << "pre: " << x->value << endl;
        } else if (v == in) {
            cout << "in: " << x->value << endl;
        } else {
            cout << "post: " << x->value << endl;
        }
        if (v == pre && x == y) {
            reachable = true;
            return true;
        }
        return false;
    }
    bool get()
    {
        return reachable;
    }
private:
    C y;
    bool reachable;
};

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
bool reachable_2(C x, C y)
{
    reachable_proc<C> proc(y);
    return aborting_traverse(x, proc).get();
}

template<typename C>
    requires(BifurcateCoordinate(C))
class tree_weight_counter
{
public:
    tree_weight_counter() : w(0) {}
    void operator()(visit v, C c)
    {
        if (v == in) w = successor(w);
    }
    WeightType(C) count()
    {
        return w;
    }
private:
    WeightType(C) w;
};

template<typename C>
    requires(BifurcateCoordinate(C))
struct input_type<tree_weight_counter<C>, 1>
{
    typedef C type;
};

template<typename C>
    requires(BifurcateCoordinate(C))
class tree_height_counter
{
public:
    typedef WeightType(C) N;
    tree_height_counter() : cur_height(0), max_height(0) {}
    void operator()(visit v, C c)
    {
        if (v == pre) {
            cur_height = successor(cur_height);
            max_height = max(cur_height, max_height);
        } else if (v == post) {
            cur_height = predecessor(cur_height);
        }
    }
    N count()
    {
        return max_height;
    }
private:
    N cur_height;
    N max_height;
};

template<typename C>
    requires(BifurcateCoordinate(C))
struct input_type<tree_height_counter<C>, 1>
{
    typedef C type;
};

template<typename T>
    requires(Regular(T))
struct input_type<plus<T>, 0>
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct input_type<less<T>, 0>
{
    typedef T type;
};

void print(int x)
{
    cout << x << endl;
}

template<int modulus>
bool congruent(int a, int b) {
    return (b - a) % modulus == 0;
}

bool test_compare_3(my_node<int>* r0, my_node<int>* r1, visit order)
{
    switch(order) {
    case pre:
        if (r0->value < r1->value) return true;
        if (r1->value < r0->value) return false;
        if (r0->left->value < r1->left->value) return true;
        if (r1->left->value < r0->left->value) return false;
        if (r0->right->value < r1->right->value) return true;
        if (r1->right->value < r0->right->value) return false;
        return false;
    case in:
        if (r0->left->value < r1->left->value) return true;
        if (r1->left->value < r0->left->value) return false;
        if (r0->value < r1->value) return true;
        if (r1->value < r0->value) return false;
        if (r0->right->value < r1->right->value) return true;
        if (r1->right->value < r0->right->value) return false;
        return false;
    case post:
        if (r0->left->value < r1->left->value) return true;
        if (r1->left->value < r0->left->value) return false;
        if (r0->right->value < r1->right->value) return true;
        if (r1->right->value < r0->right->value) return false;
        if (r0->value < r1->value) return true;
        if (r1->value < r0->value) return false;
        return false;
    }
}

int main() {
    my_node<int>* r0 = new my_node<int>(0);
    r0->new_left(0);
    r0->new_right(0);

    my_node<int>* r1 = new my_node<int>(0);
    r1->new_left(0);
    r1->left->new_right(0);

    my_node<int>* r2 = new my_node<int>(0);
    r2->new_right(0);

    my_node<int>* r3 = new my_node<int>(0);

    my_node<int>** rs = new my_node<int>*[4];
    rs[0] = r0;
    rs[1] = r1;
    rs[2] = r2;
    rs[3] = r3;

    copy(rs, rs + 4, ostream_iterator<my_node<int>*>(cout, " "));
    cout << endl;
    sort(rs, rs + 4, my_bifurcate_shape_compare<my_node<int>*, my_node<int>*>);
    copy(rs, rs + 4, ostream_iterator<my_node<int>*>(cout, " "));
    cout << endl;

    my_node<int>* r4 = new my_node<int>(1);
    r4->new_left(1)->new_left(1)->new_left(1);

    cout << rs << endl;
    cout << my_lower_bound(rs,
                           rs + 4,
                           r4,
                           my_bifurcate_shape_compare<my_node<int>*, my_node<int>*>) - rs << endl;

    /*
    for (int i = 0; i < 10000; i++) {
        r0->value = rand() % 10;
        r0->left->value = rand() % 10;
        r0->right->value = rand() % 10;
        r1->value = rand() % 10;
        r1->left->value = rand() % 10;
        r1->right->value = rand() % 10;
        cout << "(" << r0->left->value << ", " << r0->value << ", " << r0->right->value << ")";
        cout << ", (" << r1->left->value << ", " << r1->value << ", " << r1->right->value << "): ";
        assert(my_bifurcate_less(r0, r1) == test_compare_3(r0, r1, pre));
        cout << "pre ok, ";
        assert(my_bifurcate_less(r0, r1, in) == test_compare_3(r0, r1, in));
        cout << "in ok, ";
        assert(my_bifurcate_less(r0, r1, post) == test_compare_3(r0, r1, post));
        cout << "post ok" << endl;
    }
    cout << "All tests passed!" << endl;
    */

}
