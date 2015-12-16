#include <iostream>
#include <sstream>
#include "my_intrinsics.h"
#include "my_selection.h"
#include "my_type_functions.h"

using namespace std;

template<typename T1, typename T2>
bool precedes(const pair<T1, T2>& a,
              const pair<T1, T2>& b)
{
    if (a.first > b.first) return false;
    if (a.second > b.second) return false;
    if (a.first == b.first && a.second == b.second) return false;
    return true;
}

template<typename T1, typename T2>
ostream& operator<<(ostream& output, pair<T1, T2> p)
{
    stringstream combiner;
    combiner << "(" << p.first << ", " << p.second << ")";
    return (output << combiner.str());
}

bool less_than(int a, int b) {
    return a < b;
}

int main() {
    pair<int, int> a(3, 3);
    pair<int, int> b(0, 0);
    pair<int, int> c(2, 1);
    pair<int, int> d(1, 2);
    pair<int, int> e(0, 1);
    cout << select_0_4(a, b, c, d, precedes<int, int>) << endl;
    cout << select_1_4(a, b, c, d, precedes<int, int>) << endl;
    cout << select_2_4(a, b, c, d, precedes<int, int>) << endl;
    cout << select_3_4(a, b, c, d, precedes<int, int>) << endl;
    cout << median_5(a, b, d, c, e, precedes<int, int>) << endl;
    cout << my_median_5(a, b, d, c, e, precedes<int, int>) << endl;
}
