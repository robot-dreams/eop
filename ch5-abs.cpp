#include <iostream>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename T>
    requires(OrderedAdditiveGroup(T))
T abs(const T& a)
{
    if (a < T(0)) return -a;
    else          return  a;
}

int main() {
    cout << abs(-5) << endl;
}
