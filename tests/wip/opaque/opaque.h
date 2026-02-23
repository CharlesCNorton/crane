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

unsigned int safe_pred(const unsigned int n);

unsigned int pred_of_succ(const unsigned int n);

bool nat_eq_dec(const unsigned int n, const unsigned int x);

bool are_equal(const unsigned int n, const unsigned int m);

const unsigned int test_safe_pred = safe_pred((((((0 + 1) + 1) + 1) + 1) + 1));

const unsigned int test_pred_succ =
    pred_of_succ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const bool test_eq_true =
    are_equal((((((0 + 1) + 1) + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));

const bool test_eq_false =
    are_equal((((0 + 1) + 1) + 1), (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
