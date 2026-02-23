#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prim_proj.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<point> translate(const unsigned int dx, const unsigned int dy,
                                 std::shared_ptr<point> p) {
  return std::make_shared<point>(
      point{(p->px + std::move(dx)), (p->py + std::move(dy))});
}
