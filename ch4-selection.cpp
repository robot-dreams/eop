#include <iostream>
#include <sstream>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_2(const Domain(R) &a,
                            const Domain(R) &b,
                            R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return b;
    return a;
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_2(const Domain(R) &a,
                            const Domain(R) &b,
                            R r)
{
    // Precondition:
    //     weak_ordering(r)
    if (r(b, a)) return a;
    return b;
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_3(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            R r)
{
    return select_0_2(select_0_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_3(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            R r)
{
    return select_1_2(select_1_2(a, b, r), c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_3_ab(const Domain(R) &a,
                               const Domain(R) &b,
                               const Domain(R) &c,
                               R r)
{
    if (!r(c, b)) return b;
    return select_1_2(a, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_3(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            R r)
{
    if (r(b, a)) return select_1_3_ab(b, a, c, r);
    return              select_1_3_ab(a, b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_0_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    return select_0_2(select_0_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_3_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    return select_1_2(select_2_3(a, b, c, r), d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab_cd(const Domain(R) &a,
                                  const Domain(R) &b,
                                  const Domain(R) &c,
                                  const Domain(R) &d,
                                  R r)
{
    if (r(c, a)) return select_0_2(a, d, r);
    return              select_0_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4_ab(const Domain(R) &a,
                               const Domain(R) &b,
                               const Domain(R) &c,
                               const Domain(R) &d,
                               R r)
{
    if (r(d, c)) return select_1_4_ab_cd(a, b, d, c, r);
    return              select_1_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_1_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    if (r(b, a)) return select_1_4_ab(b, a, c, d ,r);
    return              select_1_4_ab(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4_ab_cd(const Domain(R) &a,
                                  const Domain(R) &b,
                                  const Domain(R) &c,
                                  const Domain(R) &d,
                                  R r)
{
    if (r(d, b)) return select_1_2(a, d, r);
    return              select_1_2(b, c, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4_ab(const Domain(R) &a,
                               const Domain(R) &b,
                               const Domain(R) &c,
                               const Domain(R) &d,
                               R r)
{
    if (r(d, c)) return select_2_4_ab_cd(a, b, d, c, r);
    return              select_2_4_ab_cd(a, b, c, d, r);
}

template<typename R>
    requires(Relation(R))
const Domain(R)& select_2_4(const Domain(R) &a,
                            const Domain(R) &b,
                            const Domain(R) &c,
                            const Domain(R) &d,
                            R r)
{
    if (r(b, a)) return select_2_4_ab(b, a, c, d ,r);
    return              select_2_4_ab(a, b, c, d, r);
}

// test code

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
    cout << select_0_4(a, b, c, d, precedes<int, int>) << endl;
    cout << select_1_4(a, b, c, d, precedes<int, int>) << endl;
    cout << select_2_4(a, b, c, d, precedes<int, int>) << endl;
    cout << select_3_4(a, b, c, d, precedes<int, int>) << endl;
}
