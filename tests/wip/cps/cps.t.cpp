// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "cps.h"

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
    // Test 1: factorial 5 = 120
    {
        ASSERT(CPS::test_fact_5 == 120);
        std::cout << "Test 1 (factorial 5): PASSED" << std::endl;
    }

    // Test 2: fibonacci 7 = 13
    {
        ASSERT(CPS::test_fib_7 == 13);
        std::cout << "Test 2 (fibonacci 7): PASSED" << std::endl;
    }

    // Test 3: tree_sum (Node (Node (Leaf 1) (Leaf 2)) (Leaf 3)) = 6
    {
        ASSERT(CPS::test_tree == 6);
        std::cout << "Test 3 (tree_sum): PASSED" << std::endl;
    }

    // Test 4: list_sum [10;20;30] = 60
    {
        ASSERT(CPS::test_list_sum == 60);
        std::cout << "Test 4 (list_sum): PASSED" << std::endl;
    }

    // Test 5: count_evens [1;2;3;4;5;6] = 3
    {
        ASSERT(CPS::test_evens == 3);
        std::cout << "Test 5 (count_evens): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll CPS tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
