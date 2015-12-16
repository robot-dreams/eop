#include <iostream>
#include "my_integer.h"
#include "my_intrinsics.h"
#include "my_iterator.h"
#include "my_type_functions.h"

using namespace std;

//
// Start Exercise 6.2
/////

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
class my_count_if_accumulator
{
public:
    my_count_if_accumulator(P p, J j) : p(p), j(j) {}

    void operator()(const ValueType(I)& x)
    {
        if (p(x)) j = successor(j);
    }

    J count() const {
        return j;
    }

private:
    P p;
    J j;
};

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
J my_count_if_2(I f, I l, P p, J j)
{
    // Precondition: readable_bounded_range(f, l)
    return my_for_each(f,
                       l,
                       my_count_if_accumulator<I, P, J>(p, j)).count();
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
DistanceType(I) my_count_if_2(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    typedef DistanceType(I) N;
    return my_for_each(f,
                       l,
                       my_count_if_accumulator<I, P, N>(p, N(0))).count();
}

//
// End Exercise 6.2
/////

template<typename I, typename P, typename J>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && Iterator(J) &&
        ValueType(I) == Domain(P))
pair<J, I> my_count_if_n_2(I f, DistanceType(I) n, P p, J j)
{
    // Precondition: readable_weak_range(f, n)
    pair<my_count_if_accumulator<I, P, J>, I> q =
        my_for_each_n(f,
                      n,
                      my_count_if_accumulator<I, P, J>(p, j));
    return pair<J, I>(q.first.count(), q.second);
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
pair<DistanceType(I), I> my_count_if_n_2(I f, DistanceType(I) n, P p)
{
    // Precondition: readable_weak_range(f, n)
    typedef DistanceType(I) N;
    pair<my_count_if_accumulator<I, P, N>, I> q =
        my_for_each_n(f,
                      n,
                      my_count_if_accumulator<I, P, N>(p, N(0)));
    return pair<N, I>(q.first.count(), q.second);
}

template<typename I, typename P>
    requires(Readable(I) && BidirectionalIterator(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_find_backward_if_2(I f, I l, P p)
{
    // Preconditions:
    //     readable_bounded_range(f, l)
    while (l != f && !p(source(predecessor(l))))
        l = predecessor(l);
    return l;
}

template<typename T>
struct input_type<less<T>, 0> {
    typedef T type;
};

template<typename T>
struct input_type<greater<T>, 0> {
    typedef T type;
};

template<typename T>
struct input_type<plus<T>, 0> {
    typedef T type;
};

template<typename T>
struct input_type<multiplies<T>, 0> {
    typedef T type;
};

template<typename I>
    requires(Readable(I) && BidirectionalIterator(I))
bool palindrome(I f, I l)
{
    if (f == l) return true;
    l = predecessor(l);
    while (f != l) {
        if (source(f) != source(l)) return false;
        f = successor(f);
        if (f == l) return true;
        l = predecessor(l);
    }
    return true;
}

int main() {
    int* x = new int[10];
    for (int i = 0; i < 10; i++) {
        x[i] = 0;
    }
    const char* s = string("asgardragsa").c_str();
    my_reverse_iterator_adapter<const char*> f(s + strlen(s));
    my_reverse_iterator_adapter<const char*> l(s);
    while (f != l) {
        cout << source(f) << endl;
        f = successor(f);
    }
    cout << boolalpha << palindrome(s, s + strlen(s)) << endl;
    delete[] x;
}
