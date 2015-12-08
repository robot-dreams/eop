#include <iomanip>
#include <iostream>
#include <string>
#include "my_intrinsics.h"
#include "my_type_functions.h"
#include "my_powers.h"

using namespace std;

string list(string lhs, string rhs) {
    return string("(") + lhs + string(" ") + rhs + string(")");
}

int multiply(int a, int b) {
    return a * b;
}

template<int modulus>
int mod_multiply(int a, int b) {
    return static_cast<int>((static_cast<long>(a) * b) % modulus);
}

void test(int (*f)(int, long, int (*)(int, int)), string name) {
    clock_t start, end;
    int result;
    start = clock();
    result = f(2, LONG_MAX, mod_multiply<19599399173>);
    end = clock();
    cout << setw(25) << name << ": " << result << ", ";
    cout << "clock ticks: " << (end - start) << endl;
}

void test_accumulate(int (*f)(int, int, long, int (*)(int, int)), string name) {
    clock_t start, end;
    int result;
    start = clock();
    result = f(1, 2, LONG_MAX, mod_multiply<19599399173>);
    end = clock();
    cout << setw(25) << name << ": " << result << ", ";
    cout << "clock ticks: " << (end - start) << endl;
}

int main() {
    cout << power_left_associated("a", 5, list) << endl;
    cout << power_right_associated("a", 5, list) << endl;
    test_accumulate(power_accumulate_positive, "power_accumulate_positive");
    test_accumulate(power_accumulate, "power_accumuate");
    test(power, "power");
    cout << "powers of two: " << endl;
    for (int n = 0; n <= 10; ++n) {
        cout << setw(5) << n << ": " << power(2, n, multiply, 1) << endl;
    }
}

