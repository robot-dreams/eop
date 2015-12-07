#ifndef MY_TYPE_FUNCTIONS
#define MY_TYPE_FUNCTIONS

#include "my_intrinsics.h"

// InputType: FunctionalProcedure x size_t -> Regular

template<typename T, size_t i>
    requires(FunctionalProcedure(T))
struct input_type;

#define InputType(T, i) typename input_type< T, i >::type

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

#endif
