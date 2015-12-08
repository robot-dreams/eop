#include <cassert>
#include <iostream>
#include "my_type_functions.h"
#include "my_integer.h"

using namespace std;

size_t failures = 0;
size_t successes = 0;

template<typename F>
void test_unary_procedure(F f,
                          string procedure,
                          string type,
                          Domain(F) n,
                          Codomain(F) expected)
{
    if (f(n) != expected) {
        ++failures;

        cout << "    test failed for procedure " << procedure;
        cout << ", type " << type << endl;

        cout << "        input: " << n;
        cout << "; expected output: " << expected;
        cout << "; actual output: " << f(n) << endl;
    } else {
        ++successes;
    }
}

template<typename F>
void test_binary_procedure(F f,
                           string procedure,
                           string type,
                           Domain(F) n1,
                           Domain(F) n2,
                           Codomain(F) expected)
{
    if (f(n1, n2) != expected) {
        ++failures;

        cout << "    test failed for procedure " << procedure;
        cout << ", type " << type << endl;

        cout << "        inputs: " << n1 << ", " << n2;
        cout << "; expected output: " << expected;
        cout << "; actual output: " << f(n1, n2) << endl;
    } else {
        ++successes;
    }
}

template<typename I>
void test_procedures_for_signed_type(string type) {
#define UNARY_TEST_CASE(PROCEDURE, INPUT, EXPECTED) test_unary_procedure(PROCEDURE<I>, #PROCEDURE, type, INPUT, EXPECTED);
#define BINARY_TEST_CASE(PROCEDURE, INPUT1, INPUT2, EXPECTED) test_binary_procedure(PROCEDURE<I>, #PROCEDURE, type, INPUT1, INPUT2, EXPECTED);
#include "my_integer_test_cases_signed.h"
#undef UNARY_TEST_CASE
#undef BINARY_TEST_CASE
}

template<typename I>
void test_procedures_for_unsigned_type(string type) {
#define UNARY_TEST_CASE(PROCEDURE, INPUT, EXPECTED) test_unary_procedure(PROCEDURE<I>, #PROCEDURE, type, INPUT, EXPECTED);
#define BINARY_TEST_CASE(PROCEDURE, INPUT1, INPUT2, EXPECTED) test_binary_procedure(PROCEDURE<I>, #PROCEDURE, type, INPUT1, INPUT2, EXPECTED);
#include "my_integer_test_cases_unsigned.h"
#undef UNARY_TEST_CASE
#undef BINARY_TEST_CASE
}

int main() {
    test_procedures_for_signed_type<short>("short");
    test_procedures_for_signed_type<int>("int");
    test_procedures_for_signed_type<long>("long");
    test_procedures_for_unsigned_type<unsigned short>("unsigned short");
    test_procedures_for_unsigned_type<unsigned int>("unsigned int");
    test_procedures_for_unsigned_type<unsigned long>("unsigned long");

    cout << successes << " tests passed" << endl;
    if (failures) {
        cout << failures << " tests failed" << endl;
    } else {
        cout << "all tests passed!" << endl;
    }
}
