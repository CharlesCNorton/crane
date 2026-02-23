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

template <typename I, typename A>
concept Numeric = requires(A a0) {
  { I::to_nat(a0) } -> std::convertible_to<unsigned int>;
};

template <typename _tcI0, typename T1> unsigned int to_nat(const T1 _x0) {
  return _tcI0::to_nat(_x0);
}

struct numNat {
  static unsigned int to_nat(unsigned int n) { return n; }
};
static_assert(Numeric<numNat, unsigned int>);

struct numBool {
  static unsigned int to_nat(bool b) {
    if (b) {
      return (0 + 1);
    } else {
      return 0;
    }
  }
};
static_assert(Numeric<numBool, bool>);

template <typename _tcI0, typename T1> unsigned int numeric_double(const T1 x) {
  return (_tcI0::to_nat(x) + _tcI0::to_nat(x));
}

template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
};

template <typename _tcI0, typename T1> bool eqb(const T1 _x0, const T1 _x1) {
  return _tcI0::eqb(_x0, _x1);
}

template <typename I, typename A>
concept Ord = requires(A a0, A a1) {
  { I::leb(a1, a0) } -> std::convertible_to<bool>;
};

template <typename _tcI0, typename _tcI1, typename T1>
bool leb(const T1 _x0, const T1 _x1) {
  return _tcI0::leb(_x0, _x1);
}

struct eqNat {
  static bool eqb(unsigned int x, unsigned int y) { return (x == y); }
};
static_assert(Eq<eqNat, unsigned int>);

struct ordNat {
  static bool leb(unsigned int x, unsigned int y) { return (x <= y); }
};
static_assert(Ord<ordNat, unsigned int>);

template <typename _tcI0, typename _tcI1, typename T1>
std::pair<T1, T1> sort_pair(const T1 x, const T1 y) {
  if (_tcI0::leb(x, y)) {
    return std::make_pair(x, y);
  } else {
    return std::make_pair(y, x);
  }
}

template <typename _tcI0, typename _tcI1, typename T1>
T1 min_of(const T1 x, const T1 y) {
  if (_tcI0::leb(x, y)) {
    return x;
  } else {
    return y;
  }
}

template <typename _tcI0, typename _tcI1, typename T1>
T1 max_of(const T1 x, const T1 y) {
  if (_tcI0::leb(x, y)) {
    return y;
  } else {
    return x;
  }
}

template <typename _tcI0, typename _tcI1, typename T1>
unsigned int describe(const T1 x, const T1 y) {
  if (_tcI0::eqb(x, y)) {
    return _tcI1::to_nat(x);
  } else {
    return (_tcI1::to_nat(x) + _tcI1::to_nat(y));
  }
}

const unsigned int test_nat = numNat::to_nat(
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

const unsigned int test_bool_true = numBool::to_nat(true);

const unsigned int test_bool_false = numBool::to_nat(false);

const unsigned int test_double = numeric_double<numNat, unsigned int>(
    (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const std::pair<unsigned int, unsigned int> test_sort_pair =
    sort_pair<ordNat, eqNat, unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1),
                                           (((0 + 1) + 1) + 1));

const unsigned int test_min = min_of<ordNat, eqNat, unsigned int>(
    ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), (((0 + 1) + 1) + 1));

const unsigned int test_max = max_of<ordNat, eqNat, unsigned int>(
    ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), (((0 + 1) + 1) + 1));

const unsigned int test_describe_eq = describe<eqNat, numNat, unsigned int>(
    (((((0 + 1) + 1) + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));

const unsigned int test_describe_ne = describe<eqNat, numNat, unsigned int>(
    (((0 + 1) + 1) + 1), (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));
