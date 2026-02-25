#include <algorithm>
#include <any>
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

struct Nat {
  static unsigned int pred(const unsigned int n);

  static unsigned int div2(const unsigned int n);
};

struct SigmaAssert {
  static unsigned int safe_pred(const unsigned int n);

  static unsigned int safe_div2(const unsigned int n);

  static inline const unsigned int test_pred =
      safe_pred((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_div2 =
      safe_div2(((((0 + 1) + 1) + 1) + 1));
};
