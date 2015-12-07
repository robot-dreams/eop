#include <iostream>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename F>
    requires(Transformation(F))
DistanceType(F) distance(Domain(F) x, Domain(F) y, F f)
{
    typedef DistanceType(F) N;
    N n = N(0);
    while (x != y) {
        x = f(x);
        n = n + N(1);
    }
    return n;
}

int increment(int x) {
    return x + 1;
}

int main() {
    cout << distance(0, 2, increment) << endl;
}
