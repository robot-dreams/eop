#ifndef MY_TYPE_FUNCTIONS
#define MY_TYPE_FUNCTIONS

#include <iostream>
#include <sstream>
#include "my_intrinsics.h"

using namespace std;

// InputType: FunctionalProcedure x size_t -> Regular

template<typename T, size_t i>
    requires(FunctionalProcedure(T))
struct input_type;

#define InputType(T, i) typename input_type< T, i >::type

template<typename T>
struct input_type<void (*)(T&), 0> {
    typedef T type;
};

template<typename T>
struct input_type<T (*)(T), 0> {
    typedef T type;
};

template<typename T>
struct input_type<T (*)(T, T), 0> {
    typedef T type;
};

// Domain: HomogeneousFunction -> Regular

#define Domain(T) InputType(T, 0)

// DistanceType: Transformation -> Integer

template<typename F>
    requires(Transformation(F))
struct distance_type;

template<>
struct distance_type<int> {
    typedef unsigned int type;
};

template<>
struct distance_type<unsigned long> {
    typedef unsigned long type;
};

template<typename T>
struct distance_type<T*> {
    typedef unsigned long type;
};

#define DistanceType(T) typename distance_type< Domain(T) >::type

template<typename T0, typename T1, typename T2>
    requires(Regular(T0), Regular(T1), Regular(T2))
struct triple
{
    T0 m0;
    T1 m1;
    T2 m2;

    triple() { }
    triple(T0 m0, T1 m1, T2 m2) : m0(m0), m1(m1), m2(m2) { }
};

template<typename T0, typename T1, typename T2>
    requires(Regular(T0), Regular(T1), Regular(T2))
bool operator==(const triple<T0, T1, T2>& x, const triple<T0, T1, T2>& y)
{
    return x.m0 == y.m0 && x.m1 == y.m1 && x.m2 == y.m2;
}

template<typename T0, typename T1, typename T2>
    requires(Regular(T0), Regular(T1), Regular(T2))
bool operator<(const triple<T0, T1, T2>& x, const triple<T0, T1, T2>& y)
{
    return x.m0 < y.m0 ||
        (!(y.m0 < x.m0) && x.m1 < y.m1) ||
        (!(y.m0 < x.m0) && !(y.m1 < x.m1) && x.m2 < y.m2);
}

template<typename T0, typename T1, typename T2>
    requires(Regular(T0), Regular(T1), Regular(T2))
ostream& operator<<(ostream& output, const triple<T0, T1, T2>& x)
{
    stringstream combiner;
    combiner << "(" << x.m0 << ", " << x.m1 << ", " << x.m2 << ")";
    output << combiner.str();
    return output;
}
#endif
