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
        if (r(lhs.first, rhs.first)) return true;
        return lhs.second < rhs.second;
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

template<typename Test, typename SR>
void test_all_permutations(Test test_j_k,
                           string procedure_name,
                           const Domain(SR)&
                               (*select)(const Domain(SR)&,
                                         const Domain(SR)&,
                                         SR),
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

int main()
{
    vector<int> v;
    v.push_back(0);
    v.push_back(1);

    test_all_permutations(test_j_2<StabilityRelation<bool (*)(int, int)> >,
                          "select_0_2",
                          select_0_2<StabilityRelation<bool (*)(int, int)> >,
                          v,
                          strengthen(less_than),
                          pair<const int&, size_t>(0, 0));

    cout << successes << " " << pluralize("test", successes) << " passed" << endl;
    if (failures) {
        cout << failures << " " << pluralize("test", failures) << " failed" << endl;
    } else {
        cout << "all tests passed!" << endl;
    }
}
