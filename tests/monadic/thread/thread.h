#include <algorithm>
#include <chrono>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <thread>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

namespace threadtest {
void fun1(const unsigned int n);

void fun2(const unsigned int n);

void test(const unsigned int m, const unsigned int n);

void test2(const unsigned int m, const unsigned int n);

}; // namespace threadtest
