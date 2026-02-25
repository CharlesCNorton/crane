#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
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

struct PrimFloatTest {
  static inline const double f_zero = 0x0p+0;

  static inline const double f_one = 0x1p+0;

  static inline const double f_neg_one = (-0x1p+0);

  static double test_add(const double, const double);

  static double test_sub(const double, const double);

  static double test_mul(const double, const double);

  static double test_div(const double, const double);

  static double test_opp(const double);

  static double test_abs(const double);

  static double test_sqrt(const double);

  static bool test_eqb(const double, const double);

  static bool test_ltb(const double, const double);

  static bool test_leb(const double, const double);

  static double test_of_uint63(const int64_t);
};
