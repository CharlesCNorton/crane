#include <colist.h>

#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>
#include <vector>

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

int nat_to_int(const std::shared_ptr<Nat::nat>& n) {
  return std::visit(Overloaded{
    [](const Nat::nat::O) -> int { return 0; },
    [](const Nat::nat::S s) -> int { return 1 + nat_to_int(s._a0); }
  }, n->v());
}

template <typename A>
std::vector<A> list_to_vec(const std::shared_ptr<List::list<A>>& l) {
  std::vector<A> result;
  auto cur = l;
  while (true) {
    bool done = std::visit(Overloaded{
      [&](const typename List::list<A>::nil) -> bool { return true; },
      [&](const typename List::list<A>::cons c) -> bool {
        result.push_back(c._a0);
        cur = c._a1;
        return false;
      }
    }, cur->v());
    if (done) break;
  }
  return result;
}

std::shared_ptr<Nat::nat> int_to_nat(int x) {
  if (x <= 0) return Nat::nat::ctor::O_();
  return Nat::nat::ctor::S_(int_to_nat(x - 1));
}

int main() {
  // Test 1: first_three should be [0, 1, 2]
  auto ft = Colist::first_three;
  auto vec = list_to_vec<std::shared_ptr<Nat::nat>>(ft);
  ASSERT(vec.size() == 3);
  ASSERT(nat_to_int(vec[0]) == 0);
  ASSERT(nat_to_int(vec[1]) == 1);
  ASSERT(nat_to_int(vec[2]) == 2);

  // Test 2: nats creates an infinite stream that doesn't diverge
  auto stream = Colist::nats(Nat::nat::ctor::O_());
  // Converting 5 elements should work without stack overflow
  auto five = stream->list_of_colist(int_to_nat(5));
  auto vec5 = list_to_vec<std::shared_ptr<Nat::nat>>(five);
  ASSERT(vec5.size() == 5);
  ASSERT(nat_to_int(vec5[0]) == 0);
  ASSERT(nat_to_int(vec5[1]) == 1);
  ASSERT(nat_to_int(vec5[2]) == 2);
  ASSERT(nat_to_int(vec5[3]) == 3);
  ASSERT(nat_to_int(vec5[4]) == 4);

  // Test 3: nats starting from a non-zero value
  auto stream5 = Colist::nats(int_to_nat(5));
  auto three = stream5->list_of_colist(int_to_nat(3));
  auto vec3 = list_to_vec<std::shared_ptr<Nat::nat>>(three);
  ASSERT(vec3.size() == 3);
  ASSERT(nat_to_int(vec3[0]) == 5);
  ASSERT(nat_to_int(vec3[1]) == 6);
  ASSERT(nat_to_int(vec3[2]) == 7);

  return testStatus;
}
