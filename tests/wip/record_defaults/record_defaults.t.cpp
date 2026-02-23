// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "record_defaults.h"

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

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
    // Test 1: default config width
    {
        ASSERT(test_default_width == 80);
        std::cout << "Test 1 (default width): PASSED" << std::endl;
    }

    // Test 2: default config debug
    {
        ASSERT(test_default_debug == false);
        std::cout << "Test 2 (default debug): PASSED" << std::endl;
    }

    // Test 3: total_cells (80 * 24 * 1 = 1920)
    {
        ASSERT(test_cells == 1920);
        std::cout << "Test 3 (total_cells): PASSED" << std::endl;
    }

    // Test 4: modified config (120 * 24 * 1 = 2880)
    {
        ASSERT(test_modified == 2880);
        std::cout << "Test 4 (modified cells): PASSED" << std::endl;
    }

    // Test 5: rect area (10 * 5 = 50)
    {
        ASSERT(test_rect_area == 50);
        std::cout << "Test 5 (rect area): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll record_defaults tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
