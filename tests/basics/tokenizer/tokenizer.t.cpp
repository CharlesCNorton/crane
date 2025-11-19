// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <tokenizer.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <string_view>
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

using namespace ToString;
using namespace Tokenizer;

int main() {

  std::string soft = " \t\n";
  std::string hard = "\\.";
  std::string input = " hello there! how..are you?\nDoes\\this work?";
  std::basic_string_view ssv = {soft.data(), soft.size()};
  std::basic_string_view hsv = {hard.data(), hard.size()};
  std::basic_string_view isv = {input.data(), input.size()};

  auto l = list_tokens(std::move(isv), std::move(ssv), std::move(hsv));

  std::cout << list_to_string<std::basic_string_view<char>>([&](std::basic_string_view<char> s) -> std::string {std::string r{s};
    return r;}, std::move(l)) << "\n";

  return 0;
}
