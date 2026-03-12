// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <type_app.h>

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

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  // Test type applications and polymorphic functions
  auto id_int = TypeApp::id_int;
  auto id_bool = TypeApp::id_bool;
  auto test_map = TypeApp::test_map;
  auto test_map_succ = TypeApp::test_map_succ;
  auto test_twice = TypeApp::test_twice;
  auto monoid_test = TypeApp::monoid_test;

  std::cout << "Type application test completed" << std::endl;
  return testStatus;
}
