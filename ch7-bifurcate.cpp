#include <cassert>
#include <iostream>
#include <stack>
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
    my_tree_iterator_adapter(visit v, C c) : v(v), c(c) {}
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
};

template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
my_tree_iterator_adapter<C> successor(my_tree_iterator_adapter<C> x)
{
    do {
        traverse_step(x.v, x.c);
        if (x.v == post && !has_predecessor(x.c)) {
            x.v = pre;
            x.c = NULL;
        }
    } while (x.v != pre);
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
    my_tree_iterator_adapter<my_node<T>*> begin()
    {
        return my_tree_iterator_adapter<my_node<T>*>(pre, this);
    }
    my_tree_iterator_adapter<my_node<T>*> end()
    {
        if (has_predecessor(this))
            return my_tree_iterator_adapter<my_node<T>*>(pre, parent);
        else
            return my_tree_iterator_adapter<my_node<T>*>(pre, NULL);
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
class reachable_proc
{
public:
    reachable_proc(C y) : y(y), reachable(false) {}
    void operator()(visit v, C x)
    {
        if (v == pre) {
            cout << "pre: " << x->value << endl;
        } else if (v == in) {
            cout << "in: " << x->value << endl;
        } else {
            cout << "post: " << x->value << endl;
        }
        if (v == pre && x == y)
            reachable = true;
    }
    bool get()
    {
        return reachable;
    }
private:
    C y;
    bool reachable;
};

/*
template<typename C>
    requires(BidirectionalBifurcateCoordinate(C))
bool reachable(C x, C y)
{
    reachable_proc<C> proc(y);
    return traverse(x, proc).get();
}
*/

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

int main() {
    my_node<int>* root = new my_node<int>(5);
    root->new_left(6)->new_left(7);
    root->left->new_right(8);
    root->new_right(4);

    my_node<int>* isolated = new my_node<int>(-1);

    int (*fun)(const my_tree_iterator_adapter<my_node<int>*>&) = source<my_node<int>*>;
    cout << my_reduce_nonempty(root->begin(), root->end(), plus<int>(), fun) << endl;
}
