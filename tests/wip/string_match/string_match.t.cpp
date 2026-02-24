// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "string_match.h"

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
    // Test 1: string constants
    {
        ASSERT(str_empty == "");
        ASSERT(str_hello == "hello");
        std::cout << "Test 1 (string constants): PASSED" << std::endl;
    }

    // Test 2: is_empty
    {
        ASSERT(test_empty_true == true);
        ASSERT(test_empty_false == false);
        std::cout << "Test 2 (is_empty): PASSED" << std::endl;
    }

    // Test 3: concatenation
    {
        ASSERT(test_cat == "foobar");
        std::cout << "Test 3 (concatenation): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll string_match tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
