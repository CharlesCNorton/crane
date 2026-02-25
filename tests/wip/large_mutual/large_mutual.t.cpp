// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "large_mutual.h"

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
    // Test 1: expr_size
    {
        ASSERT(LargeMutual::test_expr_size == 5);  // EAdd(ENum, EMul(ENum, ENum)) = 1+1+1+1+1
        std::cout << "Test 1 (expr_size): PASSED" << std::endl;
    }

    // Test 2: bexpr_size
    {
        ASSERT(LargeMutual::test_bexpr_size == 7);  // BAnd(BEq(EVar,ENum), BLt(EVar,ENum))
        std::cout << "Test 2 (bexpr_size): PASSED" << std::endl;
    }

    // Test 3: stmt_size
    {
        ASSERT(LargeMutual::test_stmt_size > 0);
        std::cout << "Test 3 (stmt_size): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll large_mutual tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
