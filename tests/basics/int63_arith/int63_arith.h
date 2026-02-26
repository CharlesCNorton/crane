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
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Int63Arith {
  static int64_t test_add(const int64_t, const int64_t);

  static int64_t test_sub(const int64_t, const int64_t);

  static int64_t test_mul(const int64_t, const int64_t);

  static int64_t test_div(const int64_t, const int64_t);

  static int64_t test_mod(const int64_t, const int64_t);

  static int64_t test_land(const int64_t, const int64_t);

  static int64_t test_lor(const int64_t, const int64_t);

  static int64_t test_lxor(const int64_t, const int64_t);

  static int64_t test_lsl(const int64_t, const int64_t);

  static int64_t test_lsr(const int64_t, const int64_t);

  static bool test_eqb(const int64_t, const int64_t);

  static bool test_ltb(const int64_t, const int64_t);

  static bool test_leb(const int64_t, const int64_t);
};
