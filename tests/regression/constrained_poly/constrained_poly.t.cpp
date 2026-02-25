// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "constrained_poly.h"

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
    // Test 1: poly_id nat
    {
        ASSERT(ConstrainedPoly::test_id_nat == 42);
        std::cout << "Test 1 (poly_id nat): PASSED" << std::endl;
    }

    // Test 2: poly_id bool
    {
        ASSERT(ConstrainedPoly::test_id_bool == true);
        std::cout << "Test 2 (poly_id bool): PASSED" << std::endl;
    }

    // Test 3: UPair field access
    {
        ASSERT(ConstrainedPoly::test_fst == 5);
        ASSERT(ConstrainedPoly::test_snd == false);
        std::cout << "Test 3 (UPair fields): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll constrained_poly tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
