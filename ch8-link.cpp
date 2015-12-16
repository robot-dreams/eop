#include <iostream>
#include "my_bifurcate.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_link.h"
#include "my_type_functions.h"

using namespace std;

template<typename I, typename S, typename Pred>
    requires(ForwardIterator(I) && ForwardLinker(S) &&
        IteratorType(S) == I &&
        UnaryPseudoPredicate(Pred) &&
        ValueType(I) == Domain(Pred))
pair< pair<I, I>, pair<I, I> >
split_linked_2(I f, I l, Pred p, S set_link)
{
    // Preconditions:
    //     bounded_range(f, l)
    I h0 = l, t0 = l;
    I h1 = l, t1 = l;
    linker_to_tail<S> link_to_tail(set_link);
    while (f != l) {
        if (p(source(f))) {
            if (h1 == l) {
                h1 = f;
                advance_tail(t1, f);
            } else {
                link_to_tail(t1, f);
            }
        } else {
            if (h0 == l) {
                h0 = f;
                advance_tail(t0, f);
            } else {
                link_to_tail(t0, f);
            }
        }
    }
    return make_pair(make_pair(h0, t0), make_pair(h1, t1));
}

template<typename T>
    requires(Regular(T))
void print(const T& x)
{
    cout << x << endl;
}

template<typename I>
    requires(Readable(I))
struct source_less
{
    bool operator()(const I& i, const I& j)
    {
        return source(i) < source(j);
    }
};

template<typename I>
struct input_type<source_less<I>, 0>
{
    typedef I type;
};

template<typename I>
    requires(Readable(I))
struct source_less_than
{
    typedef ValueType(I) T;
    T x;
    source_less_than(const T& x) : x(x) {}
    bool operator()(const I& i)
    {
        return source(i) < x;
    }
};

template<typename I>
struct input_type<source_less_than<I>, 0>
{
    typedef I type;
};

template<typename I>
struct alternating
{
    bool last;
    alternating(bool last = false) : last(last) {}
    bool operator()(const I& i)
    {
        last = !last;
        return last;
    }
};

template<typename I>
struct input_type<alternating<I>, 0>
{
    typedef I type;
};

template<typename I, typename R, typename S>
    requires(Readable(I) && ForwardIterator(I) &&
        Relation(R) && I == Domain(R) &&
        ForwardLinker(S))
pair<I, I> my_merge_sort_nonempty(I f, I l, R r, S set_link)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     f != l
    //     total_ordering(r)
    typedef pair<I, I> P;
    typedef triple<I, I, I> T;
    if (successor(f) == l) return pair<I, I>(f, f);
    pair<P, P> p = split_linked(f, l, alternating<I>(), set_link);
    P p0 = my_merge_sort_nonempty(p.first.first,
                                  p.first.second->next,
                                  r,
                                  set_link);
    p0.second->next = NULL;
    P p1 = my_merge_sort_nonempty(p.second.first,
                                  p.second.second->next,
                                  r,
                                  set_link);
    p1.second->next = NULL;
    T t = combine_linked_nonempty(p0.first,
                                  p0.second->next,
                                  p1.first,
                                  p1.second->next,
                                  r,
                                  set_link);
    return P(t.m0, my_find_last(t.m1, t.m2));
}

template<typename T>
bool less_than(T a, T b)
{
    return a < b;
}

template<typename T>
struct input_type<equal_to<T>, 0>
{
    typedef T type;
};

template<typename T>
    requires(Readable(T))
void print_source(T x)
{
    cout << source(x) << endl;
}

int main()
{
    typedef my_node<int>* C;
    C r0 = new my_node<int>(4);
    r0->new_left(2)->new_left(1);
    r0->left->new_right(3);
    r0->new_right(6)->new_left(5);
    r0->right->new_right(7);
    cout << weight_phased_rotating(r0) << endl;
}
