#include <colist.h>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

namespace nat {
std::shared_ptr<nat> O::make() { return std::make_shared<nat>(O{}); }
std::shared_ptr<nat> S::make(std::shared_ptr<nat> _a0) {
  return std::make_shared<nat>(S{_a0});
}
}; // namespace nat

namespace list {};

namespace Colist {
namespace colist {};

std::shared_ptr<colist::colist<std::shared_ptr<nat::nat>>>
nats(const std::shared_ptr<nat::nat> n) {
  return colist::cocons<std::shared_ptr<nat::nat>>::make(n,
                                                         nats(nat::S::make(n)));
}

}; // namespace Colist
