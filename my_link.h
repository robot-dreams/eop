#ifndef MY_LINK
#define MY_LINK

#include "my_bifurcate.h"
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_type_functions.h"

using namespace std;

template<typename T>
    requires(Regular(T))
struct link_node
{
    link_node(const T& value = T(),
              link_node* next = NULL,
              link_node* prev = NULL) :
        value(value), next(next), prev(prev) {}
    link_node* end()
    {
        return NULL;
    }
    template<typename U> friend link_node<U>* successor(link_node<U>* x);
    template<typename U> friend link_node<U>* predecessor(link_node<U>* x);
    T value;
    link_node* next;
    link_node* prev;
};

template<typename T>
    requires(Regular(T))
struct my_iterator_concept<link_node<T>*>
{
    typedef my_bidirectional_iterator_tag type;
};

template<typename T>
    requires(Regular(T))
struct value_type<link_node<T>*>
{
    typedef T type;
};

template<typename T>
    requires(Regular(T))
T source(link_node<T>* x)
{
    return x->value;
}

template<typename T>
    requires(Regular(T))
T& sink(link_node<T>* x)
{
    return x->value;
}

template<typename T>
    requires(Regular(T))
link_node<T>* successor(link_node<T>* x)
{
    // Precondition: x != NULL
    return x->next;
}

template<typename T>
    requires(Regular(T))
link_node<T>* predecessor(link_node<T>* x)
{
    // Precondition: x != NULL
    return x->prev;
}

template<typename T>
    requires(Regular(T))
struct link_node_forward_linker
{
    void operator()(link_node<T>* i, link_node<T>* j)
    {
        // Precondition: i != NULL
        i->next = j;
    }
};

template<typename T>
    requires(Regular(T))
struct link_node_backward_linker
{
    void operator()(link_node<T>* i, link_node<T>* j)
    {
        // Precondition: j != NULL
        j->prev = i;
    }
};

template<typename T>
    requires(Regular(T))
struct link_node_bidirectional_linker
{
    void operator()(link_node<T>* i, link_node<T>* j)
    {
        // Precondition: i != NULL && j != NULL
        i->next = j;
        j->prev = i;
    }
};

template<typename T>
    requires(Regular(T))
struct iterator_type<link_node_forward_linker<T> >
{
    typedef link_node<T>* type;
};

template<typename T>
    requires(Regular(T))
struct iterator_type<link_node_backward_linker<T> >
{
    typedef link_node<T>* type;
};

template<typename T>
    requires(Regular(T))
struct iterator_type<link_node_bidirectional_linker<T> >
{
    typedef link_node<T>* type;
};

template<typename I>
    requires(ForwardIterator(I))
void advance_tail(I& t, I& f)
{
    // Precondition: successor(f) is defined
    t = f;
    f = successor(f);
}

template<typename S>
    requires(ForwardLinker(S))
struct linker_to_tail
{
    typedef IteratorType(S) I;
    S set_link;
    linker_to_tail(const S& set_link) : set_link(set_link) {}
    void operator()(I& t, I& f)
    {
        // Precondition: successor(f) is defined
        set_link(t, f);
        advance_tail(t, f);
    }
};

template<typename S>
    requires(ForwardLinker(S))
struct iterator_type<linker_to_tail<S> >
{
    typedef IteratorType(S) type;
};

template<typename I>
    requires(ForwardIterator(I))
I my_find_last(I f, I l)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     f != l
    I t;
    do
        advance_tail(t, f);
    while (f != l);
    return t;
}

template<typename I, typename S, typename Pred>
    requires(ForwardIterator(I) && ForwardLinker(S) &&
        IteratorType(S) == I &&
        UnaryPseudoPredicate(Pred) &&
        I == Domain(Pred))
pair< pair<I, I>, pair<I, I> >
split_linked(I f, I l, Pred p, S set_link)
{
    // Preconditions:
    //     bounded_range(f, l)
    //
    // Lemma 8.2.  split_linked is precedence_preserving.
    //
    // Consider the condition
    //     C0 := (hi = l ^ ti = l) v
    //           (forall i, j in [h0, t0], if i precedes j then
    //               i also precedes j in the original input range)
    // as well as the analogous condition C1.  We prove the lemma
    // by showing that:
    //     (a) C0, C1 hold initially
    //     (b) Every block preserves C0, C1
    //
    // Note: we use the following facts:
    //     (1) In the entire body of this procedure, either
    //         t0 == l or t0 precedes f in the original input
    //         range (similarly, either t1 == l or t1 precedes f
    //         in the original input range)
    //     (2) The states correspond to the following conditions:
    //           s0, s2: successor(t0) = f
    //           s1, s3: successor(t1) = f
    typedef pair<I, I> P;
    linker_to_tail<S> link_to_tail(set_link);
    I h0 = l; I t0 = l;
    I h1 = l; I t1 = l;
    if (f == l)                                      goto s4;
    if (p(f))         { h1 = f; advance_tail(t1, f); goto s1; }
    else              { h0 = f; advance_tail(t0, f); goto s0; }
s0:
    if (f == l)                                      goto s4;
    if (p(f))         { h1 = f; advance_tail(t1, f); goto s3; }
    else              {         advance_tail(t0, f); goto s0; }
s1:
    if (f == l)                                      goto s4;
    if (p(f))         {         advance_tail(t1, f); goto s1; }
    else              { h0 = f; advance_tail(t0, f); goto s2; }
s2:
    if (f == l)                                      goto s4;
    if (p(f))         {         link_to_tail(t1, f); goto s3; }
    else              {         advance_tail(t0, f); goto s2; }
s3:
    if (f == l)                                      goto s4;
    if (p(f))         {         advance_tail(t1, f); goto s3; }
    else              {         link_to_tail(t0, f); goto s2; }
s4:
    // Exercise 8.1
    //
    // Assuming the range [h_i, t_i] is nonempty, t_i points to
    // the value of the last element of [f, l) that satisfies
    // the appropriate condition (either !p(f) or p(f), depending
    // on whether i = 0 or i = 1).  Let m be the iterator in
    // [f, l) whose value t_i points to.  Then successor(t_i)
    // is the same as successor(m) in the original input range
    //
    // To prove this, note that if we ever call
    // link_to_tail(t_i, f), then f satisfies the same condition
    // as t_i, but t_i precedes f in the original input range;
    // thus if t_i is the last iterator in the original input
    // range that satisfies the given condition (either p or !p),
    // then we never call link_to_tail(t_i, f)
    return pair<P, P>(P(h0, t0), P(h1, t1));
}

template<typename I, typename S, typename R>
    requires(ForwardIterator(I) && ForwardLinker(S) &&
        IteratorType(S) == I && PseudoRelation(R) &&
        I == Domain(R))
triple<I, I, I>
combine_linked_nonempty(I f0, I l0, I f1, I l1, R r, S set_link)
{
    // Precondtions:
    //     bounded_range(f0, l0)
    //     bounded_range(f1, l1)
    //     f0 != l0
    //     f1 != l1
    //     disjoint(f0, l0, f1, l1)
    typedef triple<I, I, I> T;
    linker_to_tail<S> link_to_tail(set_link);
    I h; I t;
    if (r(f1, f0))                  { h = f1; advance_tail(t, f1); goto s1; }
    else                            { h = f0; advance_tail(t, f0); goto s0; }
s0: // successor(t) == f0 && !r(f1, t)
    if (f0 == l0)                   {                              goto s2; }
    if (r(f1, f0))                  {         link_to_tail(t, f1); goto s1; }
    else                            {         advance_tail(t, f0); goto s0; }
s1: // successor(t) == f1 && r(t, f0)
    if (f1 == l1)                   {                              goto s3; }
    if (r(f1, f0))                  {         advance_tail(t, f1); goto s1; }
    else                            {         link_to_tail(t, f0); goto s0; }
s2: // f0 == l0 && successor(t) == f1
    set_link(t, f1); return T(h, t, l1);
s3: // f1 == l1 && successor(t) == f0
    set_link(t, f0); return T(h, t, l0);
}

template<typename I, typename S, typename R>
    requires(ForwardIterator(I) && ForwardLinker(S) &&
        IteratorType(S) == I && PseudoRelation(R) &&
        I == Domain(R))
triple<I, I, I>
combine_linked(I f0, I l0, I f1, I l1, R r, S set_link)
{
    // Precondtions:
    //     bounded_range(f0, l0)
    //     bounded_range(f1, l1)
    //     disjoint(f0, l0, f1, l1)
    typedef triple<I, I, I> T;
    if (f0 == l0) return T(f1, f1, l1);
    if (f1 == l1) return T(f0, f0, l0);
    return combine_linked_nonempty(f0, l0, f1, l1, r, set_link);
}

template<typename S>
    requires(ForwardLinker(S))
struct linker_to_head
{
    typedef IteratorType(S) I;
    S set_link;
    linker_to_head(const S& set_link) : set_link(set_link) {}
    void operator()(I& h, I& f)
    {
        // Precondition: successor(f) is defined
        I t = successor(f);
        set_link(f, h);
        h = f;
        f = t;
    }
};

template<typename S>
    requires(ForwardLinker(S))
struct iterator_type<linker_to_head<S> >
{
    typedef IteratorType(S) type;
};

template<typename I, typename S>
    requires(ForwardIterator(I) && ForwardLinker(S) &&
        IteratorType(S) == I)
I my_reverse_append(I f, I l, I h, S set_link)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     h is not in the half-open bounded range between f and l
    linker_to_head<S> link_to_head(set_link);
    while (f != l) link_to_head(h, f);
    return h;
}

template<typename I, typename P>
    requires(Readable(I) && Predicate(P) &&
        ValueType(I) == Domain(P))
struct predicate_source
{
    P p;
    predicate_source(const P& p) : p(p) {}
    bool operator()(I i)
    {
        return p(source(i));
    }
};

template<typename I, typename P>
struct input_type<predicate_source<I, P>, 0>
{
    typedef I type;
};

template<typename I, typename S, typename P>
    requires(ForwardLinker(S) && I == IteratorType(S) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair< pair<I, I>, pair<I, I> >
partition_linked(I f, I l, P p, S set_link)
{
    predicate_source<I, P> ps(p);
    return split_linked(f, l, ps, set_link);
}

template<typename I0, typename I1, typename R>
    requires(Readable(I0) && Readable(I1) &&
        ValueType(I0) == ValueType(I1) &&
        Relation(R) && ValueType(I0) == Domain(R))
struct relation_source
{
    R r;
    relation_source(const R& r) : r(r) {}
    bool operator()(const I0& i0, const I1& i1)
    {
        return r(source(i0), source(i1));
    }
};

template<typename I0, typename I1, typename R>
struct input_type<relation_source<I0, I1, R>, 0>
{
    typedef I0 type;
};

template<typename I0, typename I1, typename R>
struct input_type<relation_source<I0, I1, R>, 1>
{
    typedef I1 type;
};

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
pair<I, I> merge_linked_nonempty(I f0, I l0, I f1, I l1,
                                 R r, S set_link)
{
    // Preconditions:
    //     f0 != l0
    //     f1 != l1
    //     increasing_range(f0, l0, r)
    //     increasing_range(f1, l1, r)
    //     disjoint(f0, l0, f1, l1)
    relation_source<I, I, R> rs(r);
    triple<I, I, I> t = combine_linked_nonempty(f0, l0, f1, l1, r, set_link);
    set_link(my_find_last(t.m1, t.m2), l1);
    return pair<I, I>(t.m0, l1);
}

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
pair<I, I> sort_linked_nonempty_n(I f, DistanceType(I) n, R r, S set_link)
{
    // Preconditions:
    //     counted_range(f, n)
    //     n > 0
    //     weak_ordering(r)
    typedef DistanceType(I) N;
    typedef pair<I, I> P;
    if (n == N(1)) return P(f, successor(f));
    N h = half_nonnegative(n);
    P p0 = sort_linked_nonempty_n(f, h, r, set_link);
    P p1 = sort_linked_nonempty_n(p0.second, n - h, r, set_link);
    return merge_linked_nonempty(p0.first,
                                 p0.second,
                                 p1.first,
                                 p1.second,
                                 r,
                                 set_link);
}

template<typename I>
    requires(ForwardIterator(I))
struct sort_linked_trivial
{
    sort_linked_trivial() {}
    pair<I, I> operator()(I i)
    {
        return pair<I, I>(i, successor(i));
    }
};

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
struct sort_linked_op
{
    R r;
    S set_link;
    sort_linked_op(R r, S set_link) : r(r), set_link(set_link) {}
    typedef pair<I, I> T;
    T operator()(const T& x, const T& y)
    {
        return merge_linked_nonempty(x.first,
                                     x.second,
                                     y.first,
                                     y.second,
                                     r,
                                     set_link);
    }
};

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
struct input_type<sort_linked_op<I, S, R>, 0>
{
    typedef pair<I, I> type;
};

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
pair<I, I> sort_linked_nonempty_n_iterative(I f, DistanceType(I) n, R r, S set_link)
{
    // Preconditions:
    //     counted_range(f, n)
    //     n > 0
    //     weak_ordering(r)
    return my_reduce_balanced_n(f,
                                n,
                                sort_linked_op<I, S, R>(r, set_link),
                                sort_linked_trivial<I>(),
                                pair<I, I>(f, f));
}

template<typename R>
    requires(BinaryRelation(R))
struct equivalent_to_prev
{
    R r;
    Domain(R) prev;
    bool has_prev;
    equivalent_to_prev(const R& r) :
        r(r), prev(Domain(R)()), has_prev(false) {}
    bool operator()(const Domain(R)& curr)
    {
        bool result = false;
        if (has_prev) result = r(curr, prev);
        else has_prev = true;
        prev = curr;
        return result;
    }
};

template<typename R>
    requires(BinaryRelation(R))
struct input_type<equivalent_to_prev<R>, 0>
{
    typedef Domain(R) type;
};

template<typename I, typename S, typename R>
    requires(Readable(I) &&
        ForwardLinker(S) && I == IteratorType(S) &&
        Relation(R) && ValueType(I) == Domain(R))
pair< pair<I, I>, pair<I, I> >
unique(I f, I l, R r, S set_link)
{
    // Preconditions:
    //     bounded_range(f, l)
    //     equivalence(r)
    equivalent_to_prev<R> e(r);
    predicate_source<I, equivalent_to_prev<R> > ps(e);
    return split_linked(f, l, ps, set_link);
}

template<typename C>
    requires(EmptyLinkedBifurcateCoordinate(C))
void my_rotate(C& curr, C& prev)
{
    // Precondition: !empty(curr)
    C tmp = left_successor(curr);
    set_left_successor(curr, right_successor(curr));
    set_right_successor(curr, prev);
    if (empty(tmp)) { prev = tmp; return; }
    prev = curr;
    curr = tmp;
}

template<typename C, typename Proc>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        C == InputType(Proc, 0))
Proc traverse_rotating(C c, Proc proc)
{
    // Precondition: tree(c)
    C curr = c;
    C prev;
    do {
        proc(curr);
        my_rotate(curr, prev);
    } while (curr != c);
    do {
        proc(curr);
        my_rotate(curr, prev);
    } while (curr != c);
    proc(curr);
    my_rotate(curr, prev);
    return proc;
}

template<typename T, typename N>
    requires(Integer(N))
struct my_counter
{
    N n;
    my_counter() : n(0) {}
    my_counter(N n) : n(n) {}
    void operator()(const T&)
    {
        n = successor(n);
    }
};

template<typename T, typename N>
    requires(Integer(N))
struct input_type<my_counter<T, N>, 0>
{
    typedef T type;
};

template<typename C>
    requires(EmptyLinkedBifurcateCoordinate(C))
WeightType(C) weight_rotating(C c)
{
    // Precondition: tree(c);
    typedef WeightType(C) N;
    return traverse_rotating(c, my_counter<C, N>()).n / N(3);
}

template<typename N, typename Proc>
    requires(Integer(N) &&
        Procedure(Proc) && Arity(Proc) == 1)
struct phased_applicator
{
    N period;
    N phase;
    N n;
    // Invariant: n, phase in [0, period)
    Proc proc;
    phased_applicator(N period, N phase, N n, Proc proc) :
        period(period), phase(phase), n(n), proc(proc) { }
    void operator()(InputType(Proc, 0) x)
    {
        if (n == phase) proc(x);
        n = successor(n);
        if (n == period) n = N(0);
    }
};

template<typename C, typename Proc>
    requires(EmptyLinkedBifurcateCoordinate(C) &&
        Procedure(Proc) && Arity(Proc) == 1 &&
        C == InputType(Proc, 0))
Proc traverse_phased_rotating(C c, int phase, Proc proc)
{
    // Preconditions:
    //     tree(c)
    //     0 <= phase < 3
    phased_applicator<int, Proc> applicator(3, phase, 0, proc);
    return traverse_rotating(c, applicator).proc;
}

template<typename C>
    requires(EmptyLinkedBifurcateCoordinate(C))
WeightType(C) weight_phased_rotating(C c)
{
    // Precondition: tree(c);
    my_counter<C, WeightType(C)> proc;
    return traverse_phased_rotating(c, 0, proc).n;
}

#endif
