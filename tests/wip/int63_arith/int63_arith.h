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

const int i_zero = 0;

const int i_one = 1;

const int i_add = 10 + 20;

const int i_mul = 6 * 7;

const int i_sub = 50 - 8;

const bool i_eqb_true = 42 == 42;

const bool i_eqb_false = 42 == 43;

const bool i_ltb_true = 3 < 5;

const bool i_ltb_false = 5 < 3;

const bool i_leb_true = 3 <= 3;

const bool i_leb_false = 5 <= 3;

int i_abs(const int x);

const int test_abs_pos = i_abs(42);

const int test_abs_neg = i_abs(0 - 42);
