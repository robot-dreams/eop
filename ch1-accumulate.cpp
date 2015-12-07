#include <iostream>
#include <vector>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename Op, typename InputIterator>
    requires(BinaryOperation(Op) &&
        Domain(Op) == ValueType(InputIterator))
Domain(Op) accumulate(
        InputIterator start,
        InputIterator stop,
        Op op,
        Domain(Op) accumulator)
{
    // Preconditions:
    // - op is associative
    while (start != stop) {
        accumulator = op(*start, accumulator);
        ++start;
    }
    return accumulator;
}

template<size_t modulus>
int modular_sum(int a, int b)
{
    int result = (a + b) % modulus;
    if (result < 0) result += modulus;
    return result;
}

int main() {
    vector<int> v;
    for (int i = 1; i <= 10; i++)
        v.push_back(i);
    cout << accumulate(v.begin(), v.end(), modular_sum<9>, 0) << endl;
}
