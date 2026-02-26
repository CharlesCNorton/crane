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
#include <variant>

unsigned int
RecordDefaults::cfg_width(const std::shared_ptr<RecordDefaults::Config> &c) {
  return c->cfg_width;
}

unsigned int
RecordDefaults::cfg_height(const std::shared_ptr<RecordDefaults::Config> &c) {
  return c->cfg_height;
}

unsigned int
RecordDefaults::cfg_depth(const std::shared_ptr<RecordDefaults::Config> &c) {
  return c->cfg_depth;
}

bool RecordDefaults::cfg_debug(
    const std::shared_ptr<RecordDefaults::Config> &c) {
  return c->cfg_debug;
}

std::shared_ptr<RecordDefaults::Config>
RecordDefaults::set_width(const unsigned int w,
                          std::shared_ptr<RecordDefaults::Config> c) {
  return std::make_shared<RecordDefaults::Config>(
      Config{std::move(w), c->cfg_height, c->cfg_depth, c->cfg_debug});
}

std::shared_ptr<RecordDefaults::Config>
RecordDefaults::set_debug(const bool d,
                          std::shared_ptr<RecordDefaults::Config> c) {
  return std::make_shared<RecordDefaults::Config>(
      Config{c->cfg_width, c->cfg_height, c->cfg_depth, std::move(d)});
}

unsigned int
RecordDefaults::px(const std::shared_ptr<RecordDefaults::Point> &p) {
  return p->px;
}

unsigned int
RecordDefaults::py(const std::shared_ptr<RecordDefaults::Point> &p) {
  return p->py;
}

std::shared_ptr<RecordDefaults::Point>
RecordDefaults::origin(const std::shared_ptr<RecordDefaults::Rect> &r) {
  return r->origin;
}

std::shared_ptr<RecordDefaults::Point>
RecordDefaults::extent(const std::shared_ptr<RecordDefaults::Rect> &r) {
  return r->extent;
}

unsigned int
RecordDefaults::rect_area(const std::shared_ptr<RecordDefaults::Rect> &r) {
  return (r->extent->px * r->extent->py);
}

std::shared_ptr<RecordDefaults::Rect>
RecordDefaults::make_rect(const unsigned int x, const unsigned int y,
                          const unsigned int w, const unsigned int h) {
  return std::make_shared<RecordDefaults::Rect>(
      Rect{std::make_shared<RecordDefaults::Point>(
               Point{std::move(x), std::move(y)}),
           std::make_shared<RecordDefaults::Point>(
               Point{std::move(w), std::move(h)})});
}

unsigned int
RecordDefaults::total_cells(const std::shared_ptr<RecordDefaults::Config> &c) {
  return ((c->cfg_width * c->cfg_height) * c->cfg_depth);
}
