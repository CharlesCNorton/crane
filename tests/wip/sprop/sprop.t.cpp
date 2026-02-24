// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "sprop.h"

#include <iostream>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {
    // Test 1: guarded_pred
    {
        ASSERT(test_guarded == 4);  // guarded_pred 5 = 4
        std::cout << "Test 1 (guarded_pred): PASSED" << std::endl;
    }

    // Test 2: SProp box unboxing
    {
        ASSERT(test_box == 42);
        std::cout << "Test 2 (sbox unbox): PASSED" << std::endl;
    }

    // Test 3: safe_div
    {
        ASSERT(test_div == 3);  // safe_div 10 3 = 3
        std::cout << "Test 3 (safe_div): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll sprop tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
