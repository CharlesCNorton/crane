#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct RecordDefaults {
  struct Config {
    unsigned int cfg_width;
    unsigned int cfg_height;
    unsigned int cfg_depth;
    bool cfg_debug;
  };

  static unsigned int cfg_width(const std::shared_ptr<Config> &c);

  static unsigned int cfg_height(const std::shared_ptr<Config> &c);

  static unsigned int cfg_depth(const std::shared_ptr<Config> &c);

  static bool cfg_debug(const std::shared_ptr<Config> &c);

 static inline const std::shared_ptr<Config> default_config = std::make_shared<Config>(Config{((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), ((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), (0 + 1), false});

 static std::shared_ptr<Config> set_width(const unsigned int w,
                                          std::shared_ptr<Config> c);

 static std::shared_ptr<Config> set_debug(const bool d,
                                          std::shared_ptr<Config> c);

 struct Point {
   unsigned int px;
   unsigned int py;
 };

 static unsigned int px(const std::shared_ptr<Point> &p);

 static unsigned int py(const std::shared_ptr<Point> &p);

 struct Rect {
   std::shared_ptr<Point> origin;
   std::shared_ptr<Point> extent;
 };

 static std::shared_ptr<Point> origin(const std::shared_ptr<Rect> &r);

 static std::shared_ptr<Point> extent(const std::shared_ptr<Rect> &r);

 static unsigned int rect_area(const std::shared_ptr<Rect> &r);

 static std::shared_ptr<Rect> make_rect(const unsigned int x,
                                        const unsigned int y,
                                        const unsigned int w,
                                        const unsigned int h);

 static unsigned int total_cells(const std::shared_ptr<Config> &c);

 static inline const unsigned int test_default_width =
     default_config->cfg_width;

 static inline const bool test_default_debug = default_config->cfg_debug;

 static inline const unsigned int test_cells = total_cells(default_config);

 static inline const unsigned int test_modified = total_cells(set_width(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), set_debug(true, default_config)));

 static inline const unsigned int test_rect_area = rect_area(make_rect(
     0, 0, ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
     (((((0 + 1) + 1) + 1) + 1) + 1)));
};
