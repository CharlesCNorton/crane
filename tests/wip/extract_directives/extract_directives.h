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

unsigned int offset(const unsigned int base, const unsigned int x);

unsigned int scale(const unsigned int base, const unsigned int x);

unsigned int transform(const unsigned int base, const unsigned int x);

unsigned int safe_pred(const unsigned int n);

const unsigned int test_offset =
    offset(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
           (((((0 + 1) + 1) + 1) + 1) + 1));

const unsigned int test_scale =
    scale((((0 + 1) + 1) + 1), ((((0 + 1) + 1) + 1) + 1));

const unsigned int test_transform =
    transform(((0 + 1) + 1), (((0 + 1) + 1) + 1));

const unsigned int test_safe_pred = safe_pred((((((0 + 1) + 1) + 1) + 1) + 1));

unsigned int inner_add(const unsigned int, const unsigned int);

unsigned int inner_mul(const unsigned int, const unsigned int);

unsigned int outer_use(const unsigned int a, const unsigned int b);

const unsigned int test_inner =
    inner_add((((0 + 1) + 1) + 1), (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const unsigned int test_outer =
    outer_use(((((0 + 1) + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));
