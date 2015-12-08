#include <iostream>
#include "my_intrinsics.h"
#include "my_type_functions.h"
#include "my_powers.h"

using namespace std;

template<typename I>
    requires(Integer(I))
pair<I, I> fibonacci_matrix_multiply(const pair<I, I>& x,
                              const pair<I, I>& y)
{
    return pair<I, I>(
        x.first * (y.second + y.first) + x.second * y.first,
        x.first * y.first + x.second * y.second);
}

template<typename I>
    requires(Integer(I))
I fibonacci(I n)
{
    // Preconditions:
    //     !negative(n)
    if (zero(n)) return I(0);
    return power(pair<I, I>(I(1), I(0)),
                 n,
                 fibonacci_matrix_multiply<I>).first;
}

int main(int argc, char *argv[]) {
    cout << fibonacci(atoll(argv[1])) << endl;
}
