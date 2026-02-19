// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <sigma_assert.h>

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
    // Test safe_pred(5) = 4
    ASSERT(SigmaAssert::test_pred == 4u);

    // Test safe_div2(4) = 2
    ASSERT(SigmaAssert::test_div2 == 2u);

    if (testStatus == 0) {
        std::cout << "All sigma_assert tests passed!" << std::endl;
    }

    return testStatus;
}
