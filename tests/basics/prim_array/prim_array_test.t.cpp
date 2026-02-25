// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Test harness for PrimArray extraction via persistent_array<T>.
// Exercises: make, get, set, length, copy, persistence, OOB, chained sets.

#include <prim_array_test.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

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
    // Basic construction: freshly-made array returns default for all indices.
    ASSERT(PrimArrayTest::get_default == 0);

    // Length.
    ASSERT(PrimArrayTest::arr5_len == 5);

    // Set + read back from the modified array.
    ASSERT(PrimArrayTest::get_modified == 42);

    // Persistence: original array is unchanged after set.
    ASSERT(PrimArrayTest::get_original == 0);

    // Chained sets.
    ASSERT(PrimArrayTest::chain_0 == 10);
    ASSERT(PrimArrayTest::chain_1 == 20);
    ASSERT(PrimArrayTest::chain_2 == 30);
    ASSERT(PrimArrayTest::chain_3 == 0);  // untouched element

    // Copy produces an independent array with the same contents.
    ASSERT(PrimArrayTest::copy_val == 42);

    // OOB access returns the default value.
    ASSERT(PrimArrayTest::oob_get == 0);

    if (testStatus == 0) {
        std::cout << "All prim_array tests passed." << std::endl;
    }
    return testStatus;
}
