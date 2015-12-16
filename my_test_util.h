#ifndef MY_TEST_UTIL
#define MY_TEST_UTIL

#include "my_integer.h"
#include "my_link.h"

int* new_array_list(int n, int initial, int step)
{
    int* array = new int[n];
    for (int i = 0; i < n; ++i)
        array[i] = initial + i * step;
    return array;
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

#endif
