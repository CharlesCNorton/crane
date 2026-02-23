// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "extract_directives.h"

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
    // Test 1: offset 10 5 = 15
    {
        ASSERT(test_offset == 15);
        std::cout << "Test 1 (offset): PASSED" << std::endl;
    }

    // Test 2: scale 3 4 = 12
    {
        ASSERT(test_scale == 12);
        std::cout << "Test 2 (scale): PASSED" << std::endl;
    }

    // Test 3: transform 2 3 = scale 2 (offset 2 3) = (3+2)*2 = 10
    {
        ASSERT(test_transform == 10);
        std::cout << "Test 3 (transform): PASSED" << std::endl;
    }

    // Test 4: safe_pred 5 = 4
    {
        ASSERT(test_safe_pred == 4);
        std::cout << "Test 4 (safe_pred): PASSED" << std::endl;
    }

    // Test 5: inner_add 3 7 = 10
    {
        ASSERT(test_inner == 10);
        std::cout << "Test 5 (inner_add): PASSED" << std::endl;
    }

    // Test 6: outer_use 4 5 = inner_add 4 5 + inner_mul 4 5 = 9 + 20 = 29
    {
        ASSERT(test_outer == 29);
        std::cout << "Test 6 (outer_use): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll extract_directives tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
