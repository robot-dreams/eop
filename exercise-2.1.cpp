#include <cassert>
#include <iostream>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

bool p(int a, int b) {
    if (a < 0) return b >= INT_MIN - a;
    if (a > 0) return b <= INT_MAX - a;
    return true;
}

bool p2(int a, int b) {
    assert(sizeof(long long) > sizeof(int));
    long long sum = (long long) a + b;
    return sum >= INT_MIN && sum <= INT_MAX;
}

int main() {
    cout << boolalpha;
    cout << p2(INT_MIN, -1) << endl;
    cout << p2(INT_MAX, 1) << endl;
    cout << p2(INT_MIN / 2, INT_MIN / 2) << endl;
    cout << p2(INT_MAX / 2, INT_MAX / 2) << endl;
    cout << p2(INT_MAX / 2 + 1, INT_MAX / 2 + 1) << endl;
}
