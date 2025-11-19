#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pstring.h>
#include <string>
#include <utility>
#include <variant>

namespace nat {
std::shared_ptr<nat> O::make() { return std::make_shared<nat>(O{}); }
std::shared_ptr<nat> S::make(std::shared_ptr<nat> _a0) {
  return std::make_shared<nat>(S{_a0});
}
}; // namespace nat

namespace list {};

namespace PString {
std::string nat_to_string(const std::shared_ptr<nat::nat> n) {
  return std::visit(
      Overloaded{[&](const nat::O _args) -> std::string { return "O"; },
                 [&](const nat::S _args) -> std::string {
                   std::shared_ptr<nat::nat> n_ = _args._a0;
                   return "S" + nat_to_string(n_);
                 }},
      *n);
}

int nat_to_int(const std::shared_ptr<nat::nat> n) {
  return std::visit(Overloaded{[&](const nat::O _args) -> int { return 0; },
                               [&](const nat::S _args) -> int {
                                 std::shared_ptr<nat::nat> n_ = _args._a0;
                                 return 1 + nat_to_int(n_);
                               }},
                    *n);
}

}; // namespace PString
