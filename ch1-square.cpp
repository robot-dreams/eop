#include <iostream>
#include <string>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename Op>
    requires(BinaryOperation(Op))
Domain(Op) square(const Domain(Op)& x, Op op)
{
    return op(x, x);
}

string concatenate(string lhs, string rhs) {
    return lhs + rhs;
}

int main() {
    cout << square("hello", concatenate) << endl;
}
