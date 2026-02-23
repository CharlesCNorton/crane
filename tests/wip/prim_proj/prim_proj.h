#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
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

struct point {
  unsigned int px;
  unsigned int py;
};

const std::shared_ptr<point> origin = std::make_shared<point>(point{0, 0});

std::shared_ptr<point> translate(const unsigned int dx, const unsigned int dy,
                                 const std::shared_ptr<point> &p);
