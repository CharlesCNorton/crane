#include <algorithm>
#include <any>
#include <cassert>
#include <coercions.h>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int Coercions::bool_to_nat(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}

unsigned int Coercions::add_bool(const unsigned int n, const bool b) {
  return (n + bool_to_nat(b));
}

unsigned int Coercions::unwrap(std::shared_ptr<Coercions::wrapper> w) {
  return std::move(w);
}

unsigned int
Coercions::double_wrapped(const std::shared_ptr<Coercions::wrapper> &w) {
  return (w + w);
}

bool Coercions::unbox(std::shared_ptr<Coercions::boolBox> b) {
  return std::move(b);
}

unsigned int
Coercions::add_boolbox(const unsigned int n,
                       const std::shared_ptr<Coercions::boolBox> &bb) {
  return (n + bool_to_nat(bb));
}

unsigned int
Coercions::apply_transform(const std::shared_ptr<Coercions::transform> &t,
                           const unsigned int _x0) {
  return t(std::move(_x0));
}
