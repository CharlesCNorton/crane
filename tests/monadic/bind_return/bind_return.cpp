#include <algorithm>
#include <any>
#include <bind_return.h>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector>

int64_t bindreturn::test1() { return ignoreAndReturn<int64_t>(int64_t(42)); }

int64_t bindreturn::test2() {
  return transform<unit, int64_t>(unit::tt,
                                  [](unit _x) { return int64_t(42); });
}

int64_t bindreturn::test3() {
  return nested<unit, bool, int64_t>(
      unit::tt, [](unit _x) { return true; },
      [](bool b) {
        if (b) {
          return int64_t(1);
        } else {
          return int64_t(0);
        }
      });
}

int64_t bindreturn::test4() {
  std::vector<int64_t> v = {};
  v.push_back(int64_t(1));
  v.push_back(int64_t(2));
  v.push_back(int64_t(3));
  return v.size();
}

std::shared_ptr<List::list<int64_t>> bindreturn::intToList(const int64_t n) {
  return List::list<int64_t>::ctor::cons_(n, List::list<int64_t>::ctor::nil_());
}

std::shared_ptr<List::list<int64_t>> bindreturn::test5() {
  int64_t x = int64_t(1);
  return intToList(x);
}

int64_t bindreturn::test6() {
  unit _x = unit::tt;
  bool y = true;
  return [&](void) {
    if (y) {
      return int64_t(42);
    } else {
      return int64_t(0);
    }
  }();
}
