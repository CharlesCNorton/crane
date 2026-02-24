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

unsigned int mod3(const unsigned int n);

unsigned int classify_mod3(const unsigned int n);

unsigned int add_mod3(const unsigned int x, const unsigned int y);

const unsigned int test_mod3_0 = mod3(0);

const unsigned int test_mod3_5 = mod3((((((0 + 1) + 1) + 1) + 1) + 1));

const unsigned int test_mod3_9 =
    mod3((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const unsigned int test_classify_6 =
    classify_mod3(((((((0 + 1) + 1) + 1) + 1) + 1) + 1));

const unsigned int test_classify_7 =
    classify_mod3((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const unsigned int test_add_mod3 =
    add_mod3((((((0 + 1) + 1) + 1) + 1) + 1),
             (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
