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

bool operator<(pair<int, size_t> lhs, pair<int, size_t> rhs)
{
    return lhs.first < rhs.first;
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
        return r(lhs.first, rhs.first);
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

void test_j_2_natural(string procedure_name,
                      const pair<int, size_t>&
                          (*select_j_2)(const pair<int, size_t>&,
                                        const pair<int, size_t>&),
                      const vector<pair<int, size_t> >& v,
                      pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_2(v[0], v[1]);
    if (expected != actual) {
        cout << "    test failed for procedure " << procedure_name << endl;
        cout << "        a: " << v[0] << "; b: " << v[1];
        cout << "; expected: " << expected << "; actual: " << actual << endl;
        failures++;
    } else {
        successes++;
    }
}

void test_j_3_natural(string procedure_name,
                      const pair<int, size_t>&
                          (*select_j_3)(const pair<int, size_t>&,
                                        const pair<int, size_t>&,
                                        const pair<int, size_t>&),
                      const vector<pair<int, size_t> >& v,
                      pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_3(v[0], v[1], v[2]);
    if (expected != actual) {
        cout << "    test failed for procedure " << procedure_name << endl;
        cout << "        a: " << v[0] << "; b: " << v[1] << "; c: " << v[2];
        cout << "; expected: " << expected << "; actual: " << actual << endl;
        failures++;
    } else {
        successes++;
    }
}

void test_j_4_natural(string procedure_name,
                      const pair<int, size_t>&
                          (*select_j_4)(const pair<int, size_t>&,
                                        const pair<int, size_t>&,
                                        const pair<int, size_t>&,
                                        const pair<int, size_t>&),
                      const vector<pair<int, size_t> >& v,
                      pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_4(v[0], v[1], v[2], v[3]);
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

void test_j_5_natural(string procedure_name,
                      const pair<int, size_t>&
                          (*select_j_5)(const pair<int, size_t>&,
                                        const pair<int, size_t>&,
                                        const pair<int, size_t>&,
                                        const pair<int, size_t>&,
                                        const pair<int, size_t>&),
                      const vector<pair<int, size_t> >& v,
                      pair<int, size_t> expected)
{
    pair<int, size_t> actual = select_j_5(v[0], v[1], v[2], v[3], v[4]);
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

template<typename Test, typename Select>
void test_all_permutations(Test test_j_k,
                           string procedure_name,
                           Select select,
                           vector<int> v,
                           pair<int, size_t> expected)
{
    do {
        vector<pair<int, size_t> > augmented =
            attach_stability_indices(v);
        test_j_k(procedure_name, select, augmented, expected);
    } while (next_permutation(v.begin(), v.end()));
}

template<typename R, int k>
    requires(Relation(R))
struct select_t;

template<typename R>
    requires(Relation(R))
struct select_t<R, 2>
{
    typedef const Domain(R)& (*type)(const Domain(R)&, const Domain(R)&, R);
};

template<typename R>
    requires(Relation(R))
struct select_t<R, 3>
{
    typedef const Domain(R)& (*type)(const Domain(R)&, const Domain(R)&, const Domain(R)&, R);
};

template<typename R>
    requires(Relation(R))
struct select_t<R, 4>
{
    typedef const Domain(R)& (*type)(const Domain(R)&, const Domain(R)&, const Domain(R)&, const Domain(R)&, R);
};

template<typename R>
    requires(Relation(R))
struct select_t<R, 5>
{
    typedef const Domain(R)& (*type)(const Domain(R)&, const Domain(R)&, const Domain(R)&, const Domain(R)&, const Domain(R)&, R);
};

template<typename T, int k>
    requires(TotallyOrdered(T))
struct select_natural_t;

template<typename T>
    requires(TotallyOrdered(T))
struct select_natural_t<T, 2>
{
    typedef const T& (*type)(const T&, const T&);
};

template<typename T>
    requires(TotallyOrdered(T))
struct select_natural_t<T, 3>
{
    typedef const T& (*type)(const T&, const T&, const T&);
};

template<typename T>
    requires(TotallyOrdered(T))
struct select_natural_t<T, 4>
{
    typedef const T& (*type)(const T&, const T&, const T&, const T&);
};

template<typename T>
    requires(TotallyOrdered(T))
struct select_natural_t<T, 5>
{
    typedef const T& (*type)(const T&, const T&, const T&, const T&, const T&);
};

void run_all_test_cases()
{
    vector<int> v;

    select_t<StabilityRelation<bool (*)(int, int)>, 2>::type s2;
    select_t<StabilityRelation<bool (*)(int, int)>, 3>::type s3;
    select_t<StabilityRelation<bool (*)(int, int)>, 4>::type s4;
    select_t<StabilityRelation<bool (*)(int, int)>, 5>::type s5;

    select_natural_t<pair<int, size_t>, 2>::type sn2;
    select_natural_t<pair<int, size_t>, 3>::type sn3;
    select_natural_t<pair<int, size_t>, 4>::type sn4;
    select_natural_t<pair<int, size_t>, 5>::type sn5;

#define TEST_CASE(J, K, E0, E1, ...) v = { __VA_ARGS__ };\
    s##K = select_##J##_##K;\
    test_all_permutations(test_j_##K<StabilityRelation<bool (*)(int, int)> >,\
                          string("select_") + #J + "_" + #K,\
                          s##K,\
                          v,\
                          strengthen(less_than),\
                          pair<const int&, size_t>(E0, E1));\
    sn##K = select_##J##_##K;\
    test_all_permutations(test_j_##K##_natural,\
                          string("select_") + #J + "_" + #K,\
                          sn##K,\
                          v,\
                          pair<const int&, size_t>(E0, E1));
#define MY_TEST_CASE(J, K, E0, E1, ...) v = { __VA_ARGS__ };\
    s##K = my_select_##J##_##K;\
    test_all_permutations(test_j_##K<StabilityRelation<bool (*)(int, int)> >,\
                          string("my_select_") + #J + "_" + #K,\
                          s##K,\
                          v,\
                          strengthen(less_than),\
                          pair<const int&, size_t>(E0, E1));\
    sn##K = my_select_##J##_##K;\
    test_all_permutations(test_j_##K##_natural,\
                          string("my_select_") + #J + "_" + #K,\
                          sn##K,\
                          v,\
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
