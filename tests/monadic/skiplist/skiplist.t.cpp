// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <skiplist.h>
#include <skipnode.h>
#include <string>
#include <utility>
#include <variant>
#include <vector>

// Initialize random seed
struct RandomInit {
    RandomInit() { std::srand(42); }  // Fixed seed for reproducibility
} random_init;

int main() {
    // Run individual tests with output
    bool r1 = skiplist_test::test_insert_lookup();
    std::cout << "test_insert_lookup: " << (r1 ? "PASS" : "FAIL") << std::endl;

    bool r2 = skiplist_test::test_delete();
    std::cout << "test_delete: " << (r2 ? "PASS" : "FAIL") << std::endl;

    bool r3 = skiplist_test::test_update();
    std::cout << "test_update: " << (r3 ? "PASS" : "FAIL") << std::endl;

    bool r4 = skiplist_test::test_minimum();
    std::cout << "test_minimum: " << (r4 ? "PASS" : "FAIL") << std::endl;

    unsigned int passed = (r1 ? 1 : 0) + (r2 ? 1 : 0) + (r3 ? 1 : 0) + (r4 ? 1 : 0);
    std::cout << "SkipList tests passed: " << passed << "/4" << std::endl;

    if (passed == 4) {
        std::cout << "All tests passed!" << std::endl;
        return 0;
    } else {
        std::cout << "Some tests failed." << std::endl;
        return 1;
    }
}
