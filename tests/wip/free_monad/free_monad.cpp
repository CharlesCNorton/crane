#include <free_monad.h>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

namespace unit {
std::shared_ptr<unit> tt::make() { return std::make_shared<unit>(tt{}); }
}; // namespace unit

namespace FreeMonad {
namespace IO {};

}; // namespace FreeMonad
