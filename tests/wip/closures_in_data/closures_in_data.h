#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
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

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::shared_ptr<List::list<T2>> map(F0 &&f,
                                    const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T2>> {
                                 return List::list<T2>::ctor::nil_();
                               },
                               [&](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T2>> {
                                 T1 a = _args._a0;
                                 std::shared_ptr<List::list<T1>> l0 = _args._a1;
                                 return List::list<T2>::ctor::cons_(
                                     f(a), map<T1, T2>(f, std::move(l0)));
                               }},
                    l->v());
}

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

struct ClosuresInData {
  static inline const std::shared_ptr<
      List::list<std::function<unsigned int(unsigned int)>>>
      fn_list =
          List::list<std::function<unsigned int(unsigned int)>>::ctor::cons_(
              [](axiom x) { return (x + 1); },
              List::list<std::function<unsigned int(unsigned int)>>::ctor::
                  cons_([](unsigned int x) { return (x + x); },
                        List::list<std::function<unsigned int(unsigned int)>>::
                            ctor::cons_([](unsigned int x) { return (x * x); },
                                        List::list<std::function<unsigned int(
                                            unsigned int)>>::ctor::nil_())));

  static std::shared_ptr<List::list<unsigned int>>
  apply_all(const std::shared_ptr<
                List::list<std::function<unsigned int(unsigned int)>>> &fns,
            const unsigned int x);

  struct transform {
    std::function<unsigned int(unsigned int)> forward;
    std::function<unsigned int(unsigned int)> backward;
  };

  static unsigned int forward(const std::shared_ptr<transform> &,
                              const unsigned int);

  static unsigned int backward(const std::shared_ptr<transform> &,
                               const unsigned int);

  static inline const std::shared_ptr<transform> double_transform =
      std::make_shared<transform>(
          transform{[](unsigned int x) { return (x + x); },
                    [](unsigned int x) { return div(x, ((0 + 1) + 1)); }});

  static unsigned int apply_forward(const std::shared_ptr<transform> &t,
                                    const unsigned int x);

  static unsigned int apply_backward(const std::shared_ptr<transform> &t,
                                     const unsigned int x);

  static unsigned int
  compose_all(const std::shared_ptr<
                  List::list<std::function<unsigned int(unsigned int)>>> &fns,
              const unsigned int x);

  static inline const std::shared_ptr<
      List::list<std::function<unsigned int(unsigned int)>>>
      pipeline =
          List::list<std::function<unsigned int(unsigned int)>>::ctor::cons_(
              [](unsigned int x) { return (x + (0 + 1)); },
              List::list<std::function<unsigned int(unsigned int)>>::ctor::
                  cons_([](unsigned int x) { return (x * ((0 + 1) + 1)); },
                        List::list<std::function<unsigned int(unsigned int)>>::
                            ctor::cons_(
                                [](unsigned int x) {
                                  return (x +
                                          ((((((((((0 + 1) + 1) + 1) + 1) + 1) +
                                               1) +
                                              1) +
                                             1) +
                                            1) +
                                           1));
                                },
                                List::list<std::function<unsigned int(
                                    unsigned int)>>::ctor::nil_())));

  static unsigned int
  maybe_apply(const std::optional<std::function<unsigned int(unsigned int)>> mf,
              const unsigned int x);

  static inline const std::shared_ptr<List::list<unsigned int>> test_apply_all =
      apply_all(fn_list, (((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_forward = apply_forward(
      double_transform, (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_backward = apply_backward(
      double_transform,
      ((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1) +
        1) +
       1));

  static inline const unsigned int test_compose =
      compose_all(pipeline, (((0 + 1) + 1) + 1));

  static inline const unsigned int test_maybe_some = maybe_apply(
      std::make_optional<std::function<unsigned int(unsigned int)>>(
          [](axiom x) { return (x + 1); }),
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
       1));

  static inline const unsigned int test_maybe_none = maybe_apply(
      std::nullopt,
      ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
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
        1) +
       1));
};
