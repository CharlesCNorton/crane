#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rapply.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Nat> RApply::f(const std::shared_ptr<RApply::R> &r,
                               const std::shared_ptr<Nat> &_x0,
                               const std::shared_ptr<Nat> &_x1) {
  return r->f(_x0, _x1);
}

std::shared_ptr<Nat> RApply::_tag(const std::shared_ptr<RApply::R> &r) {
  return r->_tag;
}

std::shared_ptr<Nat> RApply::apply_record(const std::shared_ptr<RApply::R> &r,
                                          const std::shared_ptr<Nat> &a,
                                          const std::shared_ptr<Nat> &b) {
  return r->f(a, b);
}
