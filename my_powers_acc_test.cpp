#include <iomanip>
#include <iostream>
#include <string>
#include "my_intrinsics.h"
#include "my_type_functions.h"
#include "my_powers_acc.h"

using namespace std;

void list_acc_left(string& lhs, const string& rhs) {
    lhs = string("(") + lhs + string(" ") + rhs + string(")");
}

void list_acc_right(const string& lhs, string& rhs) {
    rhs = string("(") + lhs + string(" ") + rhs + string(")");
}

void multiply_acc(int& a, const int& b) {
    a = a * b;
}

template<int modulus>
void mod_multiply_acc(int& a, const int& b) {
    a = static_cast<int>((static_cast<long>(a) * b) % modulus);
}

void test_acc(void (*f)(int&, long, void (*)(int&, const int&)), string name) {
    clock_t start, end;
    start = clock();
    int result = 2;
    f(result, LONG_MAX, mod_multiply_acc<19599399173>);
    end = clock();
    cout << setw(25) << name << ": " << result << ", ";
    cout << "clock ticks: " << (end - start) << endl;
}

void test_accumulate_acc(void (*f)(int&, int, long, void (*)(int&, const int&)), string name) {
    clock_t start, end;
    start = clock();
    int result = 1;
    f(result, 2, LONG_MAX, mod_multiply_acc<19599399173>);
    end = clock();
    cout << setw(25) << name << ": " << result << ", ";
    cout << "clock ticks: " << (end - start) << endl;
}

int main() {
    string a = "a";
    power_left_associated_acc(a, 5, list_acc_left);
    cout << a << endl;

    a = "a";
    power_right_associated_acc(a, 5, list_acc_right);
    cout << a << endl;

    test_accumulate_acc(power_accumulate_positive_acc, "power_accumulate_positive_acc");
    test_accumulate_acc(power_accumulate_acc, "power_accumulate_acc");
    test_acc(power_acc, "power_acc");
    cout << "powers of two: " << endl;
    for (int n = 0; n <= 10; ++n) {
        int result = 2;
        power_acc(result, n, multiply_acc, 1);
        cout << setw(5) << n << ": " << result << endl;
    }
}

