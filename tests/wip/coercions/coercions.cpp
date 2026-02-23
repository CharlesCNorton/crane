#include <algorithm>
#include <any>
#include <cassert>
#include <coercions.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int bool_to_nat(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}

unsigned int add_bool(const unsigned int n, const bool b) {
  return (n + bool_to_nat(b));
}

unsigned int add_boolbox(const unsigned int n,
                         const std::shared_ptr<BoolBox::boolBox> &bb) {
  return (n + bool_to_nat(bb));
}
