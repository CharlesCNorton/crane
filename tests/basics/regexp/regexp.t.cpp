#include <regexp.h>

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
  std::cout << Matcher::parse_bool(Matcher::r1, Matcher::s1) << std::endl;
  std::cout << Matcher::parse_bool(Matcher::r1, Matcher::s2) << std::endl;
  std::cout << Matcher::parse_bool(Matcher::r1, Matcher::s3) << std::endl;
  std::cout << Matcher::parse_bool(Matcher::r1, Matcher::s4) << std::endl;
  return 0;
}