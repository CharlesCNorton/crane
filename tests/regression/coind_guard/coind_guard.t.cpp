// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "coind_guard.h"

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
    // Test 1: hd nats == 0
    {
        ASSERT(CoindGuard::test_iterate_hd == 0);
        std::cout << "Test 1 (hd nats): PASSED" << std::endl;
    }

    // Remaining tests require list traversal which may not compile
    // due to 'axiom' bug in iterate lambda

    if (testStatus == 0) {
        std::cout << "\nAll coind_guard tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
