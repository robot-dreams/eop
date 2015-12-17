#ifndef MY_UNDERLYING
#define MY_UNDERLYING

template<typename T>
    requires(Regular(T))
struct my_underlying_type
{
    typedef T type;
};

#define UnderlyingType(T) typename my_underlying_type< T >::type

template<typename T>
    requires(Regular(T))
const UnderlyingType(T) underlying_ref(const T& x)
{
    return reinterpret_cast<const UnderlyingType(T)&>(x);
}

template<typename T>
    requires(Regular(T))
UnderlyingType(T)& underlying_ref(T& x)
{
    return reinterpret_cast<UnderlyingType(T)&>(x);
}

template<typename I>
    requires(Iterator(I))
struct my_underlying_iterator
{
    I i;
    my_underlying_iterator(I i) : i(i) {}
};

template<typename I>
    requires(Iterator(I))
struct value_type< my_underlying_iterator<I> >
{
    typedef UnderlyingType(ValueType(I)) type;
};

template<typename I>
    requires(Iterator(I))
struct distance_type< my_underlying_iterator<I> >
{
    typedef DistanceType(I) type;
};

template<typename I>
    requires(Readable(I) && Iterator(I))
UnderlyingType(ValueType(I)) source(my_underlying_iterator<I> u)
{
    return underlying_ref(source(u.i));
}

template<typename I>
    requires(Writable(I) && Iterator(I))
UnderlyingType(ValueType(I))& sink(my_underlying_iterator<I> u)
{
    return underlying_ref(sink(u.i));
}

template<typename I>
    requires(Iterator(I))
my_underlying_iterator<I> successor(my_underlying_iterator<I> u)
{
    return my_underlying_iterator<I>(successor(u.i));
}

template<typename I>
    requires(BidirectionalIterator(I))
my_underlying_iterator<I> predecessor(my_underlying_iterator<I> u)
{
    return my_underlying_iterator<I>(predecessor(u.i));
}

#endif
