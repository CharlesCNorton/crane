// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "rec_record.h"

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
    // Test 1: rlist length
    {
        ASSERT(RecRecord::test_rlist_len == 3);
        std::cout << "Test 1 (rlist_length): PASSED" << std::endl;
    }

    // Test 2: rlist sum
    {
        ASSERT(RecRecord::test_rlist_sum == 6);  // 1 + 2 + 3
        std::cout << "Test 2 (rlist_sum): PASSED" << std::endl;
    }

    // Test 3: dept_head_name
    {
        ASSERT(RecRecord::test_dept_head_name == 42);
        std::cout << "Test 3 (dept_head_name): PASSED" << std::endl;
    }

    if (testStatus == 0) {
        std::cout << "\nAll rec_record tests passed!" << std::endl;
    } else {
        std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
    }
    return testStatus;
}
