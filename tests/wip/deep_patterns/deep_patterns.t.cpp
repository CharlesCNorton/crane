// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "deep_patterns.h"

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
    // Test 1: deep_option (Some (Some (Some 42))) = 42
    {
        ASSERT(test_deep_some == 42);
        std::cout << "Test 1 (deep_option some): PASSED" << std::endl;
    }

    // Test 2: deep_option (Some (Some None)) = 1
    {
        ASSERT(test_deep_none == 1);
        std::cout << "Test 2 (deep_option none): PASSED" << std::endl;
    }

    // Test 3: deep_pair ((1,2),(3,4)) = 10
    {
        ASSERT(test_deep_pair == 10);
        std::cout << "Test 3 (deep_pair): PASSED" << std::endl;
    }

    // Test 4: list_shape [10;20;30] = 60
    {
        ASSERT(test_shape_3 == 60);
        std::cout << "Test 4 (list_shape 3): PASSED" << std::endl;
    }

    // Test 5: list_shape [1;2;3;4;5;6] = 1+2+3+length[5;6] = 8
    {
        ASSERT(test_shape_long == 8);
        std::cout << "Test 5 (list_shape long): PASSED" << std::endl;
    }

    // Test 6: deep_sum (OLeft (ILeft 77)) = 77
    {
        ASSERT(test_deep_sum == 77);
        std::cout << "Test 6 (deep_sum): PASSED" << std::endl;
    }

    // Test 7: complex_match (Some (5, [10;20;30])) = 5+10+1 = 16
    {
        ASSERT(test_complex == 16);
        std::cout << "Test 7 (complex_match): PASSED" << std::endl;
    }

    // Test 8: guarded_match (3,7) = 7-3 = 4
    {
        ASSERT(test_guarded == 4);
        std::cout << "Test 8 (guarded_match): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll deep_patterns tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
