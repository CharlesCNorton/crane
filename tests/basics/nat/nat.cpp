#include <functional>
#include <iostream>
#include <memory>
#include <nat.h>
#include <string>
#include <variant>

namespace Nat {
namespace nat {
std::shared_ptr<nat> O::make() { return std::make_shared<nat>(O{}); }
std::shared_ptr<nat> S::make(std::shared_ptr<nat> _a0) {
  return std::make_shared<nat>(S{_a0});
}
}; // namespace nat

std::shared_ptr<nat::nat> add(const std::shared_ptr<nat::nat> m,
                              const std::shared_ptr<nat::nat> n) {
  return std::visit(
      Overloaded{
          [&](const nat::O _args) -> std::shared_ptr<nat::nat> { return n; },
          [&](const nat::S _args) -> std::shared_ptr<nat::nat> {
            std::shared_ptr<nat::nat> x = _args._a0;
            return nat::S::make(add(x, n));
          }},
      *m);
}

int nat_to_int(const std::shared_ptr<nat::nat> n) {
  return std::visit(Overloaded{[&](const nat::O _args) -> int { return 0; },
                               [&](const nat::S _args) -> int {
                                 std::shared_ptr<nat::nat> n_ = _args._a0;
                                 return 1 + nat_to_int(n_);
                               }},
                    *n);
}

}; // namespace Nat
