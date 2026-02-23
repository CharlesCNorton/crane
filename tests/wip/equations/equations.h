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

struct Nat {
  static bool leb(const unsigned int n, const unsigned int m);

  static bool ltb(const unsigned int n, const unsigned int m);

  static bool even(const unsigned int n);

  static unsigned int div2(const unsigned int n);
};

template <typename T1, typename T2, MapsTo<T2, T1, std::function<T2(T1)>> F0>
T2 FixWf(F0 &&step, const T1 x) {
  return step(x, [&](T1 y) { return FixWf<T1, T2>(step, y); });
}

template <MapsTo<unsigned int, unsigned int> F2>
unsigned int collatz_steps_clause_3(const unsigned int n, const bool refine,
                                    F2 &&collatz_steps0) {
  if (refine) {
    return (collatz_steps0(Nat::div2(std::move(n)), "dummy") + 1);
  } else {
    return (collatz_steps0((((((0 + 1) + 1) + 1) * std::move(n)) + (0 + 1)),
                           "dummy") +
            1);
  }
}

template <MapsTo<unsigned int, unsigned int> F1>
unsigned int collatz_steps_functional(const unsigned int n,
                                      F1 &&collatz_steps0) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n1 = n0 - 1;
      return collatz_steps_clause_3(n1, Nat::even(((n1 + 1) + 1)),
                                    collatz_steps0);
    }
  }
}

unsigned int collatz_steps(const unsigned int);

template <MapsTo<unsigned int, std::pair<unsigned int, unsigned int>> F3>
unsigned int gcd_clause_3(const unsigned int n, const unsigned int n0,
                          const bool refine, F3 &&gcd0) {
  if (refine) {
    return gcd0(
        std::make_pair((n + 1),
                       ((((std::move(n0) + 1) - (n + 1)) > (std::move(n0) + 1)
                             ? 0
                             : ((std::move(n0) + 1) - (n + 1))))),
        "dummy");
  } else {
    return gcd0(
        std::make_pair(((((std::move(n) + 1) - (n0 + 1)) > (std::move(n) + 1)
                             ? 0
                             : ((std::move(n) + 1) - (n0 + 1)))),
                       (n0 + 1)),
        "dummy");
  }
}

template <MapsTo<unsigned int, std::pair<unsigned int, unsigned int>> F1>
unsigned int gcd_functional(const std::pair<unsigned int, unsigned int> p,
                            F1 &&gcd0) {
  unsigned int n = p.first;
  unsigned int n0 = p.second;
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n1 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n2 = n0 - 1;
      return gcd_clause_3(n1, n2, Nat::ltb((n1 + 1), (n2 + 1)), gcd0);
    }
  }
}

unsigned int gcd(const std::pair<unsigned int, unsigned int>);

const unsigned int test_gcd = gcd(std::make_pair(
    ((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
    ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)));

const unsigned int test_collatz =
    collatz_steps(((((((0 + 1) + 1) + 1) + 1) + 1) + 1));
