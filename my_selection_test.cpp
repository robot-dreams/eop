#include <algorithm>
#include <iostream>
#include <map>
#include <sstream>
#include <vector>
#include "my_intrinsics.h"
#include "my_selection.h"
#include "my_type_functions.h"

using namespace std;

size_t failures;
size_t successes;

template<typename T1, typename T2>
ostream& operator<<(ostream& output, pair<T1, T2> p)
{
    stringstream combiner;
    combiner << "(" << p.first << ", " << p.second << ")";
    return (output << combiner.str());
}

string pluralize(string input, size_t count)
{
    if (count == 1) return input;
    return input + "s";
}

bool less_than(int a, int b)
{
    return a < b;
}

template<typename T>
pair<T, size_t> attach_stability_index(T element, size_t index)
{
    return pair<T, size_t>(element, index);
}

template<typename T> class StabilityIndexGenerator {
public:
    pair<T, size_t> operator()(const T& input)
    {
        return pair<T, size_t>(input, counts[input]++);
    }

private:
    map<T, size_t> counts;
};

template<typename T>
vector<pair<T, size_t> > attach_stability_indices(const vector<T>& elements)
{
    vector<pair<T, size_t> > result;
    transform(elements.begin(),
              elements.end(),
              back_inserter(result),
              StabilityIndexGenerator<T>());
    return result;
}

template<typename R>
    requires(Relation(R))
class StabilityRelation {
public:
    StabilityRelation(R r) : r(r) {}

    bool operator()(pair<const Domain(R)&, size_t> lhs,
                    pair<const Domain(R)&, size_t> rhs)
    {
        return lhs.first < rhs.first;
    }

private:
    R r;
};

template<typename R>
struct input_type<StabilityRelation<R>, 0>
{
    typedef pair<const Domain(R)&, size_t> type;
};

template<typename R>
    requires(Relation(R))
StabilityRelation<R> strengthen(R r)
{
    return StabilityRelation<R>(r);
}

template<typename SR>
void test_j_2(string procedure_name,
              const Domain(SR)&
                  (*select_j_2)(const Domain(SR)&,
                                const Domain(SR)&,
                                SR),
              const vector<pair<int, size_t> >& v,
              SR sr,
              pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_2(v[0], v[1], sr);
    if (expected != actual) {
        cout << "    test failed for procedure " << procedure_name << endl;
        cout << "        a: " << v[0] << "; b: " << v[1];
        cout << "; expected: " << expected << "; actual: " << actual << endl;
        failures++;
    } else {
        successes++;
    }
}

template<typename SR>
void test_j_3(string procedure_name,
              const Domain(SR)&
                  (*select_j_3)(const Domain(SR)&,
                                const Domain(SR)&,
                                const Domain(SR)&,
                                SR),
              const vector<pair<int, size_t> >& v,
              SR sr,
              pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_3(v[0], v[1], v[2], sr);
    if (expected != actual) {
        cout << "    test failed for procedure " << procedure_name << endl;
        cout << "        a: " << v[0] << "; b: " << v[1] << "; c: " << v[2];
        cout << "; expected: " << expected << "; actual: " << actual << endl;
        failures++;
    } else {
        successes++;
    }
}

template<typename SR>
void test_j_4(string procedure_name,
              const Domain(SR)&
                  (*select_j_4)(const Domain(SR)&,
                                const Domain(SR)&,
                                const Domain(SR)&,
                                const Domain(SR)&,
                                SR),
              const vector<pair<int, size_t> >& v,
              SR sr,
              pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_4(v[0], v[1], v[2], v[3], sr);
    if (expected != actual) {
        cout << "    test failed for procedure " << procedure_name << endl;
        cout << "        a: " << v[0] << "; b: " << v[1];
        cout  << "; c: " << v[2] << "; d: " << v[3];
        cout << "; expected: " << expected << "; actual: " << actual << endl;
        failures++;
    } else {
        successes++;
    }
}

template<typename SR>
void test_j_5(string procedure_name,
              const Domain(SR)&
                  (*select_j_5)(const Domain(SR)&,
                                const Domain(SR)&,
                                const Domain(SR)&,
                                const Domain(SR)&,
                                const Domain(SR)&,
                                SR),
              const vector<pair<int, size_t> >& v,
              SR sr,
              pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_5(v[0], v[1], v[2], v[3], v[4], sr);
    if (expected != actual) {
        cout << "    test failed for procedure " << procedure_name << endl;
        cout << "        a: " << v[0] << "; b: " << v[1];
        cout  << "; c: " << v[2] << "; d: " << v[3] << "; e: " << v[4];
        cout << "; expected: " << expected << "; actual: " << actual << endl;
        failures++;
    } else {
        successes++;
    }
}

template<typename Test, typename Select, typename SR>
void test_all_permutations(Test test_j_k,
                           string procedure_name,
                           Select select,
                           vector<int> v,
                           SR sr,
                           pair<int, size_t> expected)
{
    do {
        vector<pair<int, size_t> > augmented =
            attach_stability_indices(v);
        test_j_k(procedure_name, select, augmented, sr, expected);
    } while (next_permutation(v.begin(), v.end()));
}

void run_all_test_cases()
{
    vector<int> v;

#define TEST_CASE(J, K, E0, E1, ...) v = { __VA_ARGS__ };\
    test_all_permutations(test_j_##K<StabilityRelation<bool (*)(int, int)> >,\
                          string("select_") + #J + "_" + #K,\
                          select_##J##_##K<StabilityRelation<bool (*)(int, int)> >,\
                          v,\
                          strengthen(less_than),\
                          pair<const int&, size_t>(E0, E1));
#define MY_TEST_CASE(J, K, E0, E1, ...) v = { __VA_ARGS__ };\
    test_all_permutations(test_j_##K<StabilityRelation<bool (*)(int, int)> >,\
                          string("my_select_") + #J + "_" + #K,\
                          my_select_##J##_##K<StabilityRelation<bool (*)(int, int)> >,\
                          v,\
                          strengthen(less_than),\
                          pair<const int&, size_t>(E0, E1));
#include "my_selection_test_cases.h"
#undef TEST_CASE
#undef MY_TEST_CASE

}

int main()
{
    run_all_test_cases();

    cout << successes << " " << pluralize("test", successes) << " passed" << endl;
    if (failures) {
        cout << failures << " " << pluralize("test", failures) << " failed" << endl;
    } else {
        cout << "all tests passed!" << endl;
    }
}
