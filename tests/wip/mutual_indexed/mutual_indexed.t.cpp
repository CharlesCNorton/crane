// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "mutual_indexed.h"

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
    // Test 1: ELeaf has even_val 0
    {
        ASSERT(test_leaf_val == 0);
        std::cout << "Test 1 (leaf even_val): PASSED" << std::endl;
    }

    // Test 2: OddTree(10) has odd_val 10
    {
        ASSERT(test_tree1_val == 10);
        std::cout << "Test 2 (tree1 odd_val): PASSED" << std::endl;
    }

    // Test 3: EvenTree(20, OddTree(10, ELeaf)) has even_val 20
    {
        ASSERT(test_tree2_val == 20);
        std::cout << "Test 3 (tree2 even_val): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll mutual_indexed tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
