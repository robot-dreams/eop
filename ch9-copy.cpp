#include <iostream>
#include "my_copy.h"
#include "my_integer.h"
#include "my_iterator.h"
#include "my_intrinsics.h"
#include "my_link.h"
#include "my_type_functions.h"

using namespace std;

template<typename R, typename T>
    requires(BinaryRelation(R) &&
        Domain(R) == T)
struct counting_relation
{
    R r;
    int& n;
    counting_relation(R r, int& n) : r(r), n(n) {}
    bool operator()(const T& x, const T& y)
    {
        n = successor(n);
        return r(x, y);
    }
};

template<typename T>
void print(T x)
{
    cout << x << endl;
}

pair<link_node<int>*, link_node<int>*>
new_linked_list(int n, int value, int delta)
{
    // Precondition: n > 0 && n * delta <= INT_MAX
    typedef link_node<int> T;
    typedef link_node<int>* I;
    typedef link_node_bidirectional_linker<int> S;
    S set_link;
    I head = new T(value);
    I curr = head;
    n = predecessor(n);
    while (!zero(n)) {
        value = value + delta;
        set_link(curr, new T(value));
        curr = successor(curr);
        n = predecessor(n);
    }
    I end = new T(0);
    set_link(curr, end);
    return pair<I, I>(head, end);
}

int* sorted_random_array(int n, int upper)
{
    int* array = new int[n];
    for (int i = 0; i < n; ++i)
        array[i] = rand() % upper;
    sort(array, array + n);
    return array;
}

double merge_copy_average_comparisons(int n0, int n1, int upper, int trials)
{
    double result = 0.0;
    int count;
    counting_relation<less<int>, int> cr(less<int>(), count);
    for (int i = 0; i < trials; ++i) {
        int* f_i0 = sorted_random_array(n0, upper);
        int* f_i1 = sorted_random_array(n1, upper);
        int* f_o = new int[n0 + n1];
        count = 0;
        my_merge_copy(f_i0, f_i0 + n0, f_i1, f_i1 + n1, f_o, cr);
        result = result + cr.n;
        delete[] f_i0;
        delete[] f_i1;
        delete[] f_o;
    }
    return result / trials;
}

int main() {
    srand(clock());
    rand();

    int n = 10;
    int* x = sorted_random_array(n, 10);
    int* y = sorted_random_array(n, 10);

    copy(x, x + n, ostream_iterator<int>(cout, " ")); cout << endl;
    copy(y, y + n, ostream_iterator<int>(cout, " ")); cout << endl;

    cout << endl;
    my_reverse_swap_ranges_n(x + n, y, 5);

    copy(x, x + n, ostream_iterator<int>(cout, " ")); cout << endl;
    copy(y, y + n, ostream_iterator<int>(cout, " ")); cout << endl;
}
