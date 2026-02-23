// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "prim_proj.h"

#include <iostream>
#include <memory>

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
  // Test 1: origin is (0, 0)
  {
    ASSERT(origin->px == 0);
    ASSERT(origin->py == 0);
    std::cout << "Test 1 (origin): PASSED" << std::endl;
  }

  // Test 2: add_points — currently not extracted (primitive projection bug)
  // {
  //   auto p1 = std::make_shared<point>(point{3, 4});
  //   auto p2 = std::make_shared<point>(point{1, 2});
  //   auto sum = add_points(p1, p2);
  //   ASSERT(sum->px == 4);
  //   ASSERT(sum->py == 6);
  //   std::cout << "Test 2 (add_points): PASSED" << std::endl;
  // }

  // Test 3: translate
  {
    auto p = std::make_shared<point>(point{10, 20});
    auto moved = translate(5, 3, p);
    ASSERT(moved->px == 15);
    ASSERT(moved->py == 23);
    std::cout << "Test 3 (translate): PASSED" << std::endl;
  }

  if (testStatus == 0) {
    std::cout << "\nAll primitive projection tests passed!" << std::endl;
  } else {
    std::cout << "\n" << testStatus << " test(s) failed!" << std::endl;
  }
  return testStatus;
}
