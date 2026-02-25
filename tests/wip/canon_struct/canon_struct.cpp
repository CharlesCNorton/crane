#include <algorithm>
#include <any>
#include <canon_struct.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool eqb(const bool b1, const bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}

bool CanonStruct::eqb(const std::shared_ptr<CanonStruct::eqType> &e,
                      const CanonStruct::carrier _x0,
                      const CanonStruct::carrier _x1) {
  return e(_x0, _x1);
}

bool CanonStruct::same(const std::shared_ptr<CanonStruct::eqType> &e,
                       const CanonStruct::carrier _x0,
                       const CanonStruct::carrier _x1) {
  return e(_x0, _x1);
}
