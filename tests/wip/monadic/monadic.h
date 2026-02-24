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

std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                             const unsigned int y,
                                             const unsigned int q,
                                             const unsigned int u);

unsigned int div(const unsigned int x, const unsigned int y);

template <typename T1> std::optional<T1> option_return(const T1 x) {
  return std::make_optional<T1>(x);
}

template <typename T1, typename T2, MapsTo<std::optional<T2>, T1> F1>
std::optional<T2> option_bind(const std::optional<T1> ma, F1 &&f) {
  if (ma.has_value()) {
    T1 a = *ma;
    return f(a);
  } else {
    return std::nullopt;
  }
}

std::optional<unsigned int> safe_div(const unsigned int n,
                                     const unsigned int m);

std::optional<unsigned int> safe_sub(const unsigned int n,
                                     const unsigned int m);

std::optional<unsigned int>
div_then_sub(const unsigned int a, const unsigned int b, const unsigned int c);

const std::optional<unsigned int> test_return = option_return<unsigned int>(
    ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
                                        1) +
                                       1) +
                                      1) +
                                     1) +
                                    1) +
                                   1) +
                                  1) +
                                 1) +
                                1) +
                               1) +
                              1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1) +
     1));

const std::optional<unsigned int> test_bind_some =
    option_bind<unsigned int, unsigned int>(
        std::make_optional<unsigned int>(
            ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
        [](unsigned int x) {
          return std::make_optional<unsigned int>((x + (0 + 1)));
        });

const std::optional<unsigned int> test_bind_none =
    option_bind<unsigned int, unsigned int>(std::nullopt, [](unsigned int x) {
      return std::make_optional<unsigned int>((x + (0 + 1)));
    });

const std::optional<unsigned int> test_safe_div_ok =
    safe_div(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
             (((0 + 1) + 1) + 1));

const std::optional<unsigned int> test_safe_div_zero =
    safe_div(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), 0);

const std::optional<unsigned int> test_chain_ok = div_then_sub(
    ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1) +
     1),
    ((((0 + 1) + 1) + 1) + 1), ((0 + 1) + 1));

const std::optional<unsigned int> test_chain_fail = div_then_sub(
    ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1) +
       1) +
      1) +
     1),
    0, ((0 + 1) + 1));
