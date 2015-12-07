#include <iostream>
#include <sstream>
#include <string>
#include "my_intrinsics.h"
#include "my_type_functions.h"

using namespace std;

template<typename F, typename N>
    requires(Transformation(F) && Integer(N))
Domain(F) power_unary(Domain(F) x, N n, F f)
{
    // Preconditions:
    // - n >= 0
    // - (forall i in N) 0 < i <= n implies f^i(x) is defined
    while (n > N(0)) {
        x = f(x);
        n = n - N(1);
    }
    return x;
}

string heighway_dragon_step(string input) {
    stringstream appender;
    for (int i = 0; i < input.length(); i++) {
        switch(input[i]) {
            case 'a':
                appender << "aRbFR";
                break;
            case 'b':
                appender << "LFaLb";
                break;
            default:
                appender << input[i];
        }
    }
    return appender.str();
}

int main() {
    cout << power_unary("Fa", 10, heighway_dragon_step).length() << endl;
}

