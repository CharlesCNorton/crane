// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "where_clause.h"

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
    // Test 1: eval Plus
    {
        ASSERT(test_eval_plus == 7);  // 3 + 4
        std::cout << "Test 1 (eval Plus): PASSED" << std::endl;
    }

    // Test 2: eval Times
    {
        ASSERT(test_eval_times == 30);  // 5 * 6
        std::cout << "Test 2 (eval Times): PASSED" << std::endl;
    }

    // Test 3: eval nested
    {
        ASSERT(test_eval_nested == 7);  // (2*3) + 1
        std::cout << "Test 3 (eval nested): PASSED" << std::endl;
    }

    // Test 4: expr_size
    {
        ASSERT(test_size == 5);  // Plus(Times(Num,Num), Num) = 1+1+1+1+1
        std::cout << "Test 4 (expr_size): PASSED" << std::endl;
    }

    // Test 5: beval
    {
        ASSERT(test_beval == true);  // BAnd BTrue (BNot BFalse)
        std::cout << "Test 5 (beval): PASSED" << std::endl;
    }

    // Test 6: aeval
    {
        ASSERT(test_aeval == 10);  // AIf (BAnd T T) 10 20 => 10
        std::cout << "Test 6 (aeval): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll where_clause tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
