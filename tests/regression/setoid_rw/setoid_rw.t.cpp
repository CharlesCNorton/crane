// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "setoid_rw.h"

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
    // Test 1: mod3
    {
        ASSERT(SetoidRw::test_mod3_0 == 0);   // 0 mod 3 = 0
        ASSERT(SetoidRw::test_mod3_5 == 2);   // 5 mod 3 = 2
        ASSERT(SetoidRw::test_mod3_9 == 0);   // 9 mod 3 = 0
        std::cout << "Test 1 (mod3): PASSED" << std::endl;
    }

    // Test 2: classify_mod3
    {
        ASSERT(SetoidRw::test_classify_6 == 0);  // 6 mod 3 = 0
        ASSERT(SetoidRw::test_classify_7 == 1);  // 7 mod 3 = 1
        std::cout << "Test 2 (classify_mod3): PASSED" << std::endl;
    }

    // Test 3: add_mod3
    {
        ASSERT(SetoidRw::test_add_mod3 == 0);  // (5+7) mod 3 = 12 mod 3 = 0
        std::cout << "Test 3 (add_mod3): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll setoid_rw tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
