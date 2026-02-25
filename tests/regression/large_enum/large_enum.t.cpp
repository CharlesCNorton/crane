// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "large_enum.h"

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
    // Test 1: color_to_nat
    {
        ASSERT(LargeEnum::test_red == 0);
        ASSERT(LargeEnum::test_pink == 11);
        std::cout << "Test 1 (color_to_nat): PASSED" << std::endl;
    }

    // Test 2: is_warm
    {
        ASSERT(LargeEnum::test_warm_red == true);
        ASSERT(LargeEnum::test_warm_blue == false);
        std::cout << "Test 2 (is_warm): PASSED" << std::endl;
    }

    // Test 3: is_neutral
    {
        ASSERT(LargeEnum::test_neutral_black == true);
        ASSERT(LargeEnum::test_neutral_red == false);
        std::cout << "Test 3 (is_neutral): PASSED" << std::endl;
    }

    // Test 4: tok_to_nat
    {
        ASSERT(LargeEnum::test_tok_num == 42);
        ASSERT(LargeEnum::test_tok_plus == 100);
        ASSERT(LargeEnum::test_tok_ident == 203);
        ASSERT(LargeEnum::test_tok_eof == 999);
        std::cout << "Test 4 (tok_to_nat): PASSED" << std::endl;
    }

    // Test 5: is_operator
    {
        ASSERT(LargeEnum::test_is_op_plus == true);
        ASSERT(LargeEnum::test_is_op_num == false);
        std::cout << "Test 5 (is_operator): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll large_enum tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
