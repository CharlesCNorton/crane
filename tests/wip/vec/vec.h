#include <algorithm>
#include <any>
#include <array>
#include <cassert>
#include <cstdint>
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

struct Vec {
  static inline const std::array<int64_t, int64_t> test1 =
      []() -> std::array<int64_t, int64_t(5)> {
    std::array<int64_t, int64_t(5)> _arr;
    _arr.fill(int64_t(12));
    return _arr;
  }();

  static inline const int64_t test2 = test1.size();

  static inline const std::optional<int64_t> test3 =
      []() -> std::optional<int64_t> {
    if (int64_t(3) < int64_t(5)) {
      return std::make_optional<int64_t>(test1[int64_t(3)]);
    } else {
      return std::nullopt;
    }
  }();

  static inline const std::array<int64_t, int64_t> test4 =
      []() -> std::array<int64_t, int64_t(5)> {
    std::array<int64_t, int64_t(5)> _arr = test1;
    if (int64_t(2) < int64_t(5)) {
      _arr[int64_t(2)] = int64_t(14);
    }
    return _arr;
  }();
};
