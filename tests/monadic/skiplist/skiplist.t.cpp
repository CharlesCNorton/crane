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
    unsigned int passed = 0;
    unsigned int total = 12;

    // Original tests
    bool r1 = skiplist_test::test_insert_lookup();
    std::cout << "test_insert_lookup: " << (r1 ? "PASS" : "FAIL") << std::endl;
    if (r1) passed++;

    bool r2 = skiplist_test::test_delete();
    std::cout << "test_delete: " << (r2 ? "PASS" : "FAIL") << std::endl;
    if (r2) passed++;

    bool r3 = skiplist_test::test_update();
    std::cout << "test_update: " << (r3 ? "PASS" : "FAIL") << std::endl;
    if (r3) passed++;

    bool r4 = skiplist_test::test_minimum();
    std::cout << "test_minimum: " << (r4 ? "PASS" : "FAIL") << std::endl;
    if (r4) passed++;

    // BDE-compatible operation tests
    bool r5 = skiplist_test::test_length_isEmpty();
    std::cout << "test_length_isEmpty: " << (r5 ? "PASS" : "FAIL") << std::endl;
    if (r5) passed++;

    bool r6 = skiplist_test::test_front_back();
    std::cout << "test_front_back: " << (r6 ? "PASS" : "FAIL") << std::endl;
    if (r6) passed++;

    bool r7 = skiplist_test::test_popFront();
    std::cout << "test_popFront: " << (r7 ? "PASS" : "FAIL") << std::endl;
    if (r7) passed++;

    bool r8 = skiplist_test::test_addUnique();
    std::cout << "test_addUnique: " << (r8 ? "PASS" : "FAIL") << std::endl;
    if (r8) passed++;

    bool r9 = skiplist_test::test_find();
    std::cout << "test_find: " << (r9 ? "PASS" : "FAIL") << std::endl;
    if (r9) passed++;

    bool r10 = skiplist_test::test_navigation();
    std::cout << "test_navigation: " << (r10 ? "PASS" : "FAIL") << std::endl;
    if (r10) passed++;

    bool r11 = skiplist_test::test_bounds();
    std::cout << "test_bounds: " << (r11 ? "PASS" : "FAIL") << std::endl;
    if (r11) passed++;

    bool r12 = skiplist_test::test_removeAll();
    std::cout << "test_removeAll: " << (r12 ? "PASS" : "FAIL") << std::endl;
    if (r12) passed++;

    std::cout << "SkipList tests passed: " << passed << "/" << total << std::endl;

    if (passed == total) {
        std::cout << "All tests passed!" << std::endl;
        return 0;
    } else {
        std::cout << "Some tests failed." << std::endl;
        return 1;
    }
}
