#include <algorithm>
#include <any>
#include <cassert>
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

enum class unit { tt };

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<List::list<A>> nil_uptr() {
        return std::unique_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::unique_ptr<List::list<A>>
      cons_uptr(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::unique_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                             const unsigned int y,
                                             const unsigned int q,
                                             const unsigned int u);

unsigned int div(const unsigned int x, const unsigned int y);

template <typename T1, typename T2, MapsTo<T1, T1, T2> F0>
T1 fold_left(F0 &&f, const std::shared_ptr<List::list<T2>> &l, const T1 a0) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<T2>::nil _args) -> T1 { return a0; },
          [&](const typename List::list<T2>::cons _args) -> T1 {
            T2 b = _args._a0;
            std::shared_ptr<List::list<T2>> l0 = _args._a1;
            return fold_left<T1, T2>(f, std::move(l0), f(a0, b));
          }},
      l->v());
}

struct Monadic {
  template <typename T1> static std::optional<T1> option_return(const T1 x) {
    return std::make_optional<T1>(x);
  }

  template <typename T1, typename T2, MapsTo<std::optional<T2>, T1> F1>
  static std::optional<T2> option_bind(const std::optional<T1> ma, F1 &&f) {
    if (ma.has_value()) {
      T1 a = *ma;
      return f(a);
    } else {
      return std::nullopt;
    }
  }

  static std::optional<unsigned int> safe_div(const unsigned int n,
                                              const unsigned int m);

  static std::optional<unsigned int> safe_sub(const unsigned int n,
                                              const unsigned int m);

  static std::optional<unsigned int> div_then_sub(const unsigned int a,
                                                  const unsigned int b,
                                                  const unsigned int c);

  template <typename s, typename a>
  using State = std::function<std::pair<a, s>(s)>;

  template <typename T1, typename T2>
  static State<T1, T2> state_return(const T2 x, const T1 s) {
    return std::make_pair(x, s);
  }

  template <typename T1, typename T2, typename T3,
            MapsTo<std::pair<T2, T1>, T1> F0,
            MapsTo<std::pair<T3, T1>, T2, T1> F1>
  static State<T1, T3> state_bind(F0 &&ma, F1 &&f, const T1 s) {
    T2 a = ma(s).first;
    T1 s_ = ma(s).second;
    return f(a, s_);
  }

  template <typename T1>
  static inline const State<T1, T1> state_get =
      [](T1 s) { return std::make_pair(s, s); };

  template <typename T1>
  static State<T1, unit> state_put(const T1 s, const T1 _x) {
    return std::make_pair(unit::tt, s);
  }

  template <typename T1>
  static State<unsigned int, unsigned int>
  count_elements(const std::shared_ptr<List::list<T1>> &l) {
    return fold_left<State<unsigned int, unsigned int>, T1>(
        [](std::function<std::pair<unsigned int, unsigned int>(unsigned int)>
               acc,
           T1 _x) {
          return state_bind<unsigned int, unsigned int, unsigned int>(
              acc, [](unsigned int _x0) {
                return state_bind<unsigned int, unsigned int, unsigned int>(
                    state_get<unsigned int>, [](unsigned int n) {
                      return state_bind<unsigned int, unit, unsigned int>(
                          state_put<unsigned int>((n + 1)), [&](unit _x1) {
                            return state_return<unsigned int, unsigned int>(n);
                          });
                    });
              });
        },
        l, state_return<unsigned int, unsigned int>(0));
  }

  static inline const std::optional<unsigned int> test_return = option_return<
      unsigned int>((
      (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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

  static inline const std::optional<unsigned int> test_bind_some =
      option_bind<unsigned int, unsigned int>(
          std::make_optional<unsigned int>(
              ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
          [](unsigned int x) {
            return std::make_optional<unsigned int>((x + (0 + 1)));
          });

  static inline const std::optional<unsigned int> test_bind_none =
      option_bind<unsigned int, unsigned int>(std::nullopt, [](unsigned int x) {
        return std::make_optional<unsigned int>((x + (0 + 1)));
      });

  static inline const std::optional<unsigned int> test_safe_div_ok =
      safe_div(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
               (((0 + 1) + 1) + 1));

  static inline const std::optional<unsigned int> test_safe_div_zero = safe_div(
      ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), 0);

  static inline const std::optional<unsigned int> test_chain_ok = div_then_sub(
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

  static inline const std::optional<unsigned int> test_chain_fail =
      div_then_sub(
          ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
           1),
          0, ((0 + 1) + 1));

  static inline const std::pair<unsigned int, unsigned int> test_state =
      count_elements<unsigned int>(
          List::list<unsigned int>::ctor::cons_(
              (0 + 1),
              List::list<unsigned int>::ctor::cons_(
                  ((0 + 1) + 1),
                  List::list<unsigned int>::ctor::cons_(
                      (((0 + 1) + 1) + 1),
                      List::list<unsigned int>::ctor::cons_(
                          ((((0 + 1) + 1) + 1) + 1),
                          List::list<unsigned int>::ctor::cons_(
                              (((((0 + 1) + 1) + 1) + 1) + 1),
                              List::list<unsigned int>::ctor::nil_()))))),
          0);
};
