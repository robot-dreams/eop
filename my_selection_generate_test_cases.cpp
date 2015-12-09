#include <cassert>
#include <iostream>
#include <map>
#include <vector>

using namespace std;

vector<int> ascend(size_t k, unsigned int mask)
{
    assert(k > 0);

    vector<int> result;
    result.push_back(0);

    int current = 0;
    for (size_t i = 1; i < k; ++i) {
        if (mask & 1) current++;
        result.push_back(current);
        mask /= 2;
    }

    return result;
}

pair<int, size_t> expected(size_t j, size_t k, vector<int> v)
{
    map<int, size_t> counts;
    for (size_t i = 0; i < j; ++i) {
        ++counts[v[i]];
    }
    return pair<int, size_t>(v[j], counts[v[j]]);
}

void generate_test_cases(string macro, size_t j, size_t k) {
    for (unsigned int mask = 0; mask < (1 << (k - 1)); ++mask) {
        vector<int> v = ascend(k, mask);
        pair<int, size_t> p = expected(j, k, v);
        cout << macro << "(" << j << ", " << k << ", ";
        cout << p.first << ", " << p.second;
        for (size_t i = 0; i < v.size(); ++i)
            cout << ", " << v[i];
        cout << ")" << endl;
    }
}

int main() {
    for (size_t k = 2; k <= 4; ++k)
        for (size_t j = 0; j < k; ++j)
            generate_test_cases("TEST_CASE", j, k);
    generate_test_cases("TEST_CASE", 2, 5);
    generate_test_cases("MY_TEST_CASE", 2, 5);
}
