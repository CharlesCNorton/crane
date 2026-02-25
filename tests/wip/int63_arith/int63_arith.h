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

struct Int63Arith {
  static inline const int64_t i_zero = 0;

  static inline const int64_t i_one = 1;

  static inline const int64_t i_add = ((10 + 20) & 0x7FFFFFFFFFFFFFFFLL);

  static inline const int64_t i_mul = ((6 * 7) & 0x7FFFFFFFFFFFFFFFLL);

  static inline const int64_t i_sub = ((50 - 8) & 0x7FFFFFFFFFFFFFFFLL);

  static inline const bool i_eqb_true = (42 == 42);

  static inline const bool i_eqb_false = (42 == 43);

  static inline const bool i_ltb_true = (3 < 5);

  static inline const bool i_ltb_false = (5 < 3);

  static inline const bool i_leb_true = (3 <= 3);

  static inline const bool i_leb_false = (5 <= 3);

  static int64_t i_abs(const int64_t x);

  static inline const int64_t test_abs_pos = i_abs(42);

  static inline const int64_t test_abs_neg =
      i_abs(((0 - 42) & 0x7FFFFFFFFFFFFFFFLL));
};
