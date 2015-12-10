#include <iostream>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename I>
    requires(Iterator(I))
I successor(const I& x)
{
    return x + 1;
}

template<typename I>
    requires(Iterator(I))
void increment(I& x)
{
    // Precondition: successor(x) is defined
    x = successor(x);
}

template<typename I>
    requires(Iterator(I))
const I operator+(I f, DistanceType(I) n)
{
    // Precondition: n >= 0 && weak_range(f, n)
    while (!zero(n)) {
        f = successor(f);
        n = predecessor(n);
    }
    return f;
}

template<typename I>
    requires(Iterator(I))
DistanceType(I) operator-(I l, I f)
{
    // Precondition: bounded_range(f, l)
    DistanceType(I) n(0);
    while (f != l) {
        n = successor(n);
        f = successor(f);
    }
    return n;
}

template<typename I, typename Proc>
    requires(Iterator(I) && Readable(I) &&
        Procedure(Proc) && Arity(Op) = 1 &&
        ValueType(I) == InputType(Proc, 0))
Proc my_for_each(I f, I l, Proc proc)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l) {
        proc(source(f));
        f = successor(f);
    }
    return proc;
}

template<typename I>
    requires(Iterator(I) && Readable(I))
I my_find(I f, I l, const ValueType(I)& x)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && source(f) != x) f = successor(f);
    return f;
}

template<typename I>
    requires(Iterator(I) && Readable(I))
I my_find_not(I f, I l, const ValueType(I)& x)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && source(f) == x) f = successor(f);
    return f;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_find_if(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && !p(source(f))) f = successor(f);
    return f;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
I my_find_if_not(I f, I l, P p)
{
    // Precondition: readable_bounded_range(f, l)
    while (f != l && p(source(f))) f = successor(f);
    return f;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_all(I f, I l, P p)
{
    return my_find_if_not(f, l, p) == l;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_none(I f, I l, P p)
{
    return my_find_if(f, l, p) == l;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_not_all(I f, I l, P p)
{
    return my_find_if_not(f, l, p) != l;
}

template<typename I, typename P>
    requires(Iterator(I) && Readable(I) &&
        UnaryPredicate(P) && ValueType(I) == Domain(P))
bool my_some(I f, I l, P p)
{
    return my_find_if(f, l, p) != l;
}

template<typename T>
class PrintAndAccumulate {
public:
    PrintAndAccumulate() : accumulator(T()) {}

    void operator()(T input) {
        accumulator += input;
        cout << input << endl;
    }

    T get() {
        return accumulator;
    }

private:
    T accumulator;
};

template<typename T>
struct input_type<PrintAndAccumulate<T>, 0> {
    typedef T type;
};

void my_print(int x) {
    cout << x << endl;
}

int main() {
    int* x = new int[10];
    for (int i = 0; i < 5; i++) {
        x[i] = i;
        x[5 + i] = i;
    }
    PrintAndAccumulate<int> p = my_for_each(x, x + 5, PrintAndAccumulate<int>());
    cout << "accumulated: " << p.get() << endl;
    cout << boolalpha;
    cout << my_some(x, x + 5, bind2nd(equal_to<int>(), -1)) << endl;
    cout << my_some(x, x + 5, bind2nd(less<int>(), 5)) << endl;
    delete[] x;
}
