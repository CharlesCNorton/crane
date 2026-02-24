#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <record_defaults.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Config> set_width(const unsigned int w,
                                  std::shared_ptr<Config> c) {
  return std::make_shared<Config>(
      Config{std::move(w), c->cfg_height, c->cfg_depth, c->cfg_debug});
}

std::shared_ptr<Config> set_debug(const bool d, std::shared_ptr<Config> c) {
  return std::make_shared<Config>(
      Config{c->cfg_width, c->cfg_height, c->cfg_depth, std::move(d)});
}

std::shared_ptr<Rect> make_rect(const unsigned int x, const unsigned int y,
                                const unsigned int w, const unsigned int h) {
  return std::make_shared<Rect>(
      Rect{std::make_shared<Point>(Point{std::move(x), std::move(y)}),
           std::make_shared<Point>(Point{std::move(w), std::move(h)})});
}
