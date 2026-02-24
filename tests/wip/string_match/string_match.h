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

const std::string str_empty = "";

const std::string str_hello = "hello";

const std::string str_world = "world";

const std::string str_cat = "hello " + "world";

const int str_len_empty = "".length();

const int str_len_hello = "hello".length();

bool is_empty(const std::string s);

const bool test_empty_true = is_empty("");

const bool test_empty_false = is_empty("x");

const std::string test_cat = "foo" + "bar";
