#include <algorithm>
#include <array>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

namespace Vec {
const std::array<int, int> test1 = []() -> std::array<int, 5> {
  std::array<int, 5> _arr;
  _arr.fill(12);
  return _arr;
}();

const int test2 = test1.size();

const std::optional<int> test3 = []() -> std::optional<int> {
  if (3 < 5) {
    return std::make_optional<int>(test1[3]);
  } else {
    return std::nullopt;
  }
}();

const std::array<int, int> test4 = []() -> std::array<int, 5> {
  std::array<int, 5> _arr = test1;
  if (2 < 5) {
    _arr[2] = 14;
  }
  return _arr;
}();

}; // namespace Vec
