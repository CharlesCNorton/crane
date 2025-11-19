#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <top.h>
#include <utility>
#include <variant>

namespace list {};

std::shared_ptr<list::list<unsigned int>> seq(const unsigned int start,
                                              const unsigned int len) {
  if (len <= 0) {
    return list::nil<unsigned int>::make();
  } else {
    unsigned int len0 = len - 1;
    return list::cons<unsigned int>::make(start, seq((start + 1), len0));
  }
}
