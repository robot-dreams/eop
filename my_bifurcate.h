#ifndef MY_BIFURCATE
#define MY_BIFURCATE

#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_orbit_structure.h"
#include "my_type_functions.h"

using namespace std;

enum visit { pre, in, post };

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
class my_tree_iterator_adapter
{
public:
    my_tree_iterator_adapter(visit v, C c, visit order = pre) : v(v), c(c), order(order) {}
    bool operator==(const my_tree_iterator_adapter& other) {
        return v == other.v && c == other.c;
    }
    bool operator!=(const my_tree_iterator_adapter& other) {
        return v != other.v || c != other.c;
    }
    template<typename C0> friend my_tree_iterator_adapter<C0> successor(my_tree_iterator_adapter<C0> x);
    template<typename C0> friend ValueType(C0) source(const my_tree_iterator_adapter<C0>& x);
private:
    visit v;
    C c;
    visit order;
};

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
my_tree_iterator_adapter<C> successor(my_tree_iterator_adapter<C> x)
{
    traverse_step(x.v, x.c, x.order);
    return x;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
ValueType(C) source(const my_tree_iterator_adapter<C>& x)
{
    return source(x.c);
}

template<typename C>
struct value_type<my_tree_iterator_adapter<C> > {
    typedef ValueType(C) type;
};

template<typename C>
struct distance_type<my_tree_iterator_adapter<C> > {
    typedef WeightType(C) type;
};

template<typename T>
    requires(Regular(T))
struct my_node
{
    my_node(const T& value = T(),
            my_node* left = NULL,
            my_node* right = NULL,
            my_node* parent = NULL) :
        value(value), parent(parent), left(left), right(right) {}
    my_node* new_left(const T& value = T(),
                      my_node* left = NULL,
                      my_node* right = NULL)
    {
        this->left = new my_node(value, left, right, this);
        return this->left;
    }
    my_node* new_right(const T& value = T(),
                       my_node* left = NULL,
                       my_node* right = NULL)
    {
        this->right = new my_node(value, left, right, this);
        return this->right;
    }
    my_tree_iterator_adapter<my_node<T>*> begin(visit order = pre)
    {
        visit v = pre;
        my_node* c = this;
        if (order != pre) traverse_step(v, c, order);
        return my_tree_iterator_adapter<my_node<T>*>(v, c, order);
    }
    my_tree_iterator_adapter<my_node<T>*> end(visit order = pre)
    {
        visit v = post;
        my_node* c = this;
        traverse_step(v, c, order);
        return my_tree_iterator_adapter<my_node<T>*>(v, c, order);
    }
    T value;
    my_node* left;
    my_node* right;
    my_node* parent;
};

template<typename T>
    requires(Regular(T))
struct value_type<my_node<T>*>
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
struct weight_type<T*>
{
    typedef unsigned long type;
};

template<typename T>
    requires(Regular(T))
T source(my_node<T>* x)
{
    return x->value;
}

template<typename T>
    requires(Regular(T))
bool empty(my_node<T>* node)
{
    return node == NULL;
}

template<typename T>
    requires(Regular(T))
bool has_left_successor(my_node<T>* node)
{
    return node->left != NULL;
}

template<typename T>
    requires(Regular(T))
my_node<T>* left_successor(my_node<T>* node)
{
    return node->left;
}

template<typename T>
    requires(Regular(T))
bool has_right_successor(my_node<T>* node)
{
    return node->right != NULL;
}

template<typename T>
    requires(Regular(T))
my_node<T>* right_successor(my_node<T>* node)
{
    return node->right;
}

template<typename T>
    requires(Regular(T))
void set_right_successor(my_node<T>* node, my_node<T>* right)
{
    node->right = right;
}

template<typename T>
    requires(Regular(T))
void set_left_successor(my_node<T>* node, my_node<T>* left)
{
    node->left = left;
}

template<typename T>
    requires(Regular(T))
bool has_predecessor(my_node<T>* node)
{
    return node->parent != NULL;
}

template<typename T>
    requires(Regular(T))
my_node<T>* predecessor(my_node<T>* node)
{
    return node->parent;
}

template<typename T>
    requires(BidirectionalBifurcateCoordinate(T))
bool is_left_successor(T j)
{
    // Precondition: has_predecessor(j);
    T i = predecessor(j);
    return has_left_successor(i) && left_successor(i) == j;
}

template<typename T>
    requires(BidirectionalBifurcateCoordinate(T))
bool is_right_successor(T j)
{
    // Precondition: has_predecessor(j);
    T i = predecessor(j);
    return has_right_successor(i) && right_successor(i) == j;
}

template<typename C>
    requires(BifurcateCoordinate(C))
WeightType(C) weight_recursive(C c)
{
    // Precondition: tree(c)
    typedef WeightType(C) N;
    if (empty(c)) return N(0);
    N l(0);
    N r(0);
    if (has_left_successor(c))
        l = weight_recursive(left_successor(c));
    if (has_right_successor(c))
        r = weight_recursive(right_successor(c));
    return successor(l + r);
}

template<typename C>
    requires(BifurcateCoordinate(C))
WeightType(C) height_recursive(C c)
{
    // Precondition: tree(c)
    typedef WeightType(C) N;
    if (empty(c)) return N(0);
    N l(0);
    N r(0);
    if (has_left_successor(c))
        l = height_recursive(left_successor(c));
    if (has_right_successor(c))
        r = height_recursive(right_successor(c));
    return successor(max(l, r));
}

template<typename C, typename Proc>
    requires(BifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(P) == 2 &&
        InputType(P, 0) == visit &&
        InputType(P, 1) == C)
Proc traverse_nonempty(C c, Proc proc)
{
    // Precondition: tree(c) && !empty(c)
    proc(pre, c);
    if (has_left_successor(c))
        proc = traverse_nonempty(left_successor(c), proc);
    proc(in, c);
    if (has_right_successor(c))
        proc = traverse_nonempty(right_successor(c), proc);
    proc(post, c);
    return proc;
}

template<typename C, typename Proc>
    requires(BidirectionalBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(P) == 2 &&
        InputType(P, 0) == visit &&
        InputType(P, 1) == C)
Proc traverse_nonempty_iter(C c, Proc proc)
{
    // Precondition: tree(c) && !empty(c)
    visit v = pre;
    while (true) {
        if (v == pre) {
            proc(pre, c);
            if (has_left_successor(c)) {
                c = left_successor(c);
            } else {
                v = in;
            }
        } else if (v == in) {
            proc(in, c);
            if (has_right_successor(c)) {
                c = right_successor(c);
                v = pre;
            } else {
                v = post;
            }
        } else if (v == post) {
            proc(post, c);
            if (has_predecessor(c)) {
                if (is_left_successor(c)) {
                    v = in;
                } else {
                    // has_predecessor(c) && !is_left_successor(c)
                    // implies is_right_successor(c)
                    v = post;
                }
                c = predecessor(c);
            } else {
                return proc;
            }
        }
    }
}

// returns change in height
template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
int traverse_step(visit& v, C& c)
{
    // Precondition: has_predecessor(c) v v != post
    switch(v) {
    case pre:
        if (has_left_successor(c)) {
            c = left_successor(c);
            return 1;
        } else {
            v = in;
            return 0;
        }
    case in:
        if (has_right_successor(c)) {
            v = pre;
            c = right_successor(c);
            return 1;
        } else {
            v = post;
            return 0;
        }
    case post:
        if (is_left_successor(c)) v = in;
        c = predecessor(c);
        return -1;
    }
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
void traverse_step(visit& v, C& c, visit order)
{
    do {
        if (v == post && !has_predecessor(c)) {
            v = order;
            c = NULL;
        } else {
            traverse_step(v, c);
        }
    } while (v != order);
}

template<typename C, typename Proc>
    requires(BidirectionalBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(P) == 2 &&
        InputType(P, 0) == visit &&
        InputType(P, 1) == C)
Proc traverse(C c, Proc proc)
{
    // Precondition: tree(c)
    if (empty(c)) return proc;
    C root = c;
    visit v = pre;
    proc(pre, c);
    do {
        traverse_step(v, c);
        proc(v, c);
    } while (c != root || v != post);
    return proc;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
bool reachable(C x, C y)
{
    // Precondition: tree(x)
    if (empty(x)) return false;
    C root = x;
    visit v = pre;
    do {
        if (x == y) return true;
        traverse_step(v, x);
    } while (x != root || v != post);
    return false;
}

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
WeightType(C) weight(C c)
{
    // Precondition: tree(x)
    typedef WeightType(C) N;
    if (empty(c)) return N(0);
    N n(1);
    C root = c;
    visit v = pre;
    do {
        traverse_step(v, c);
        if (v == pre) n = successor(n);
    } while (c != root || v != post);
    return n;
}

template<typename C>
    requires(BifurcateCoordinate(C))
WeightType(C) height(C c)
{
    // Precondition: tree(c)
    typedef WeightType(C) N;
    if (empty(c)) return N(0);
    N n(1); // Invariant: n is max of height of pre visits so far
    N m(1); // Invariant: m is height of current pre visit
    C root = c;
    visit v = pre;
    do {
        m = (m - N(1)) + N(traverse_step(v, c) + 1);
        n = max(n, m);
    } while (c != root || v != post);
    return n;
}

//
// Exercise 7.3
/////

template<typename C>
    requires(BifurcateCoordinate(C))
pair<visit, C> traverse_step_transformation(pair<visit, C> x)
{
    traverse_step(x.first, x.second);
    return x;
}

template<typename C>
    requires(BifurcateCoordinate(C))
bool traverse_step_transformation_defined(pair<visit, C> x)
{
    return x.first != post || has_predecessor(x.second);
}

template<typename C>
    requires(BifurcateCoordinate(C))
bool dag(C c)
{
    return terminating(pair<visit, C>(pre, c),
                       traverse_step_transformation<C>,
                       traverse_step_transformation_defined<C>);
}

//
// End Exercise 7.3
/////

template<typename C0, typename C1>
    requires(BifurcateCoordinate(C0) &&
        BifurcateCoordinate(C1))
bool bifurcate_isomorphic_nonempty(C0 c0, C1 c1)
{
    // Preconditions:
    //    tree(c0)
    //    tree(c1)
    //    !empty(c0)
    //    !empty(c1)
    bool l0 = has_left_successor(c0);
    bool l1 = has_left_successor(c1);
    if (l0 != l1)
        return false;
    if (l0 && l1 && !bifurcate_isomorphic_nonempty(left_successor(c0),
                                                   left_successor(c1)))
        return false;
    bool r0 = has_right_successor(c0);
    bool r1 = has_right_successor(c1);
    if (r0 != r1)
        return false;
    if (r1 && l1 && !bifurcate_isomorphic_nonempty(right_successor(c0),
                                                   right_successor(c1)))
        return false;
    return true;
}

template<typename C0, typename C1>
    requires(BidirectionalBifurcateCoordinate(C0) &&
        BidirectionalBifurcateCoordinate(C1))
bool bidirectional_bifurcate_isomorphic(C0 c0, C1 c1)
{
    // Preconditions:
    //     tree(c0)
    //     tree(c1)
    if (empty(c0)) return empty(c1);
    if (empty(c1)) return false;
    C0 root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return false;
        if (c0 == root0 && v0 == post) return true;
    }
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && BoundedRange(I1) &&
        ValueType(I0) == ValueType(i1) &&
        Relation(R) && ValueType(I0) == Domain(R))
bool lexicographical_equivalent(I0 f0, I0 l0, I1 f1, I1 l1, R r)
{
    // Preconditions:
    //     readable_bounded_range(f0, l0)
    //     readable_bounded_range(f1, l1)
    //     equivalence(e)
    pair<I0, I1> p = my_find_mismatch(f0, l0, f1, l1, r);
    return p.first == l0 && p.second == l1;
}

template<typename T>
    requires(Regular(T))
struct my_equal
{
    bool operator()(const T& x, const T& y)
    {
        return x == y;
    }
};

template<typename I0, typename I1>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && BoundedRange(I1) &&
        ValueType(I0) == ValueType(i1))
bool lexicographical_equal(I0 f0, I0 l0, I1 f1, I1 l1)
{
    // Preconditions:
    //     readable_bounded_range(f0, l0)
    //     readable_bounded_range(f1, l1)
    return lexicographical_equivalent(f0, l0, f1, l1, my_equal< ValueType(I0) >());
}

template<typename C0, typename C1, typename R>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1) &&
        Relation(R) && ValueType(C0) == Domain(R))
bool bifurcate_equivalent_nonempty(C0 c0, C1 c1, R r)
{
    // Preconditions:
    //     readable_tree(c0)
    //     readable_tree(c1)
    //     !empty(c0)
    //     !empty(c1)
    if (!r(source(c0), source(c1))) return false;
    bool l0 = has_left_successor(c0);
    bool l1 = has_left_successor(c1);
    if (l0 != l1)
        return false;
    if (l0 && l1 && !bifurcate_equivalent_nonempty(left_successor(c0),
                                                   left_successor(c1),
                                                   r))
        return false;
    bool r0 = has_right_successor(c0);
    bool r1 = has_right_successor(c1);
    if (r0 != r1)
        return false;
    if (r1 && l1 && !bifurcate_equivalent_nonempty(right_successor(c0),
                                                   right_successor(c1),
                                                   r))
        return false;
    return true;
}

template<typename C0, typename C1>
    requires(Readable(C0) && BifurcateCoordinate(C0) &&
        Readable(C1) && BifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1))
bool bifurcate_equal_nonempty(C0 c0, C1 c1)
{
    // Preconditions:
    //     readable_tree(c0)
    //     readable_tree(c1)
    //     !empty(c0)
    //     !empty(c1)
    return bifurcate_equivalent_nonempty(c0, c1, equal_to< ValueType(C1) >());
}

template<typename C0, typename C1, typename R>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) &&
        BidirectionalBifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1) &&
        Relation(R) && ValueType(C0) == Domain(R))
bool bifurcate_equivalent(C0 c0, C1 c1, R r)
{
    // Preconditions:
    //     readable_tree(c0)
    //     readable_tree(c1)
    //     equivalence(r)
    if (empty(c0)) return empty(c1);
    if (empty(c1)) return false;
    C0 root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    while (true) {
        if (v0 == pre && !r(source(c0), source(c1)))
            return false;
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 != v1) return false;
        if (c0 == root0 && v0 == post) return true;
    }
}

template<typename C0, typename C1>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) && BidirectionalBifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1))
bool bifurcate_equal(C0 c0, C1 c1)
{
    // Preconditions:
    //     readable_tree(c0)
    //     readable_tree(c1)
    return bifurcate_equivalent(c0, c1, equal_to< ValueType(C0) >());
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Relation(R) && ValueType(I0) == Domain(R))
bool my_lexicographical_compare(I0 f0, I0 l0, I1 f1, I1 l1, R r)
{
    // Preconditions:
    //     readable_weak_range(f0, l0)
    //     readable_weak_range(f1, l1)
    //     weak_ordering(r)
    while (true) {
        // Exercise 7.4. Explain why the third and fourth if
        // statements can be interchanged, but the first and
        // second cannot.
        //
        // By weak trichotomy, exactly one of
        // r(source(f0), source(f1)) and
        // r(source(f1), source(f0)) can hold; thus
        // the order of the third and fourth if
        // statements if irrelevant
        //
        // On the other hand, it is possible for
        // both f0 == l0 and f1 == l1 to hold;
        // in the case where they both hold, we
        // want to return false (since in this
        // case, the two ranges are considered
        // equal, i.e. the first range is not less
        // than the second); interchanging the
        // first and second if statements would
        // cause the procedure to incorrectly
        // return true in this case
        //
        // Exercise 7.5. Explain why we did not implement this
        // procedure by using find_mismatch.
        //
        // If we had used find_mismatch along with a
        // function object that returns true on
        // equivalence (i.e. f(a, b) returns true if
        // neither r(a, b) nor r(b, a) hold), then
        // in the case where there is a position in
        // the ranges for which either r(a, b) or
        // r(b, a) holds, the return value p of
        // find_mismatch only allows us to infer that
        // one of r(p.first, p.second) or
        // r(p.second, p.first) holds, but it does
        // not allow us to determine which of the two
        // holds (even though the process of
        // determining that either r(a, b) or r(b, a)
        // holds produces enough information to
        // determine which of the two holds).  Thus
        // by avoiding find_mismatch, we avoid this
        // extra redundant call to r at the end.
        if (f1 == l1) return false;
        if (f0 == l0) return true;
        if (r(source(f0), source(f1))) return true;
        if (r(source(f1), source(f0))) return false;
        f0 = successor(f0);
        f1 = successor(f1);
    }
}

template<typename T>
    requires(TotallyOrdered(T))
struct my_less
{
    bool operator()(const T& x, const T& y)
    {
        return x < y;
    }
};

template<typename I0, typename I1>
    requires(Readable(I0) && Iterator(I0) &&
        Readable(I1) && Iterator(I1) &&
        ValueType(I0) == ValueType(I1))
bool my_lexicographical_less(I0 f0, I0 l0, I1 f1, I1 l1)
{
    // Preconditions:
    //     readable_weak_range(f0, l0)
    //     readable_weak_range(f1, l1)
    return my_lexicographical_compare(f0,
                                      l0,
                                      f1,
                                      l1,
                                      my_less< ValueType(I0) >());
}

template<typename C0, typename C1, typename R>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) &&
        BidirectionalBifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1) &&
        Relation(R) && ValueType(C0) == Domain(R))
bool my_bifurcate_compare(C0 c0, C1 c1, R r, visit order = pre)
{
    // Preconditions:
    //     readable_tree(c0)
    //     readable_tree(c1)
    //     weak_ordering(r)
    if (empty(c1)) return false;
    if (empty(c0)) return true;
    C0 root0 = c0;
    visit v0 = pre;
    visit v1 = pre;
    if (order == pre) {
        if (r(source(c0), source(c1))) return true;
        if (r(source(c1), source(c0))) return false;
    }
    while (true) {
        traverse_step(v0, c0);
        traverse_step(v1, c1);
        if (v0 == order) {
            if (r(source(c0), source(c1))) return true;
            if (r(source(c1), source(c0))) return false;
        }
        // In the case v0 != v1, one of c0 or c1 descended
        // into a subtree, while the other did not; if ci
        // descended into a subtree, then vi = pre; if
        // v1 descended into a subtree, then we return
        // true, and otherwise we return false
        if (v0 != v1) return v1 == pre;
        if (c0 == root0 && v0 == post) return false;
    }
}

template<typename C0, typename C1>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) &&
        BidirectionalBifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1))
bool my_bifurcate_less(C0 c0, C1 c1, visit order = pre)
{
    return my_bifurcate_compare(c0, c1, less< ValueType(C0) >(), order);
}

template<typename T>
struct always_false
{
    bool operator()(const T& x, const T& y)
    {
        return false;
    }
};

template<typename C0, typename C1>
    requires(Readable(C0) &&
        BidirectionalBifurcateCoordinate(C0) &&
        Readable(C1) &&
        BidirectionalBifurcateCoordinate(C1) &&
        ValueType(C0) == ValueType(C1))
bool my_bifurcate_shape_compare(C0 c0, C1 c1)
{
    return my_bifurcate_compare(c0, c1, always_false< ValueType(C0) >());
}

#endif
