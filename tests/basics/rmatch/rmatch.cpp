#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rmatch.h>
#include <string>
#include <utility>
#include <variant>

namespace RMatch {
unsigned int f1(const std::shared_ptr<MyRec> m) { return m->f1; }

unsigned int f2(const std::shared_ptr<MyRec> m) { return m->f2; }

unsigned int f3(const std::shared_ptr<MyRec> m) { return m->f3; }

unsigned int sum(const std::shared_ptr<MyRec> r) {
  return [&](void) {
    unsigned int n1 = r->f1;
    unsigned int n2 = r->f2;
    unsigned int n3 = r->f3;
    return ((n1 + n2) + n3);
  }();
}

}; // namespace RMatch
