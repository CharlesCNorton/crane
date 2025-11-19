#include <functional>
#include <iostream>
#include <memory>
#include <nested_tree.h>
#include <optional>
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

namespace NestedTree {
namespace tree {};

}; // namespace NestedTree
