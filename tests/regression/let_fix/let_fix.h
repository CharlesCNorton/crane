#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

struct LetFix {
  static unsigned int
  local_sum(const std::shared_ptr<List::list<unsigned int>> &l);

  template <typename T1>
  static std::shared_ptr<List::list<T1>>
  local_rev(const std::shared_ptr<List::list<T1>> &l) {
    std::function<std::shared_ptr<List::list<T1>>(
        std::shared_ptr<List::list<T1>>, std::shared_ptr<List::list<T1>>)>
        go;
    go = [&](std::shared_ptr<List::list<T1>> acc,
             std::shared_ptr<List::list<T1>> xs)
        -> std::shared_ptr<List::list<T1>> {
      return std::visit(
          Overloaded{
              [&](const typename List::list<T1>::nil _args)
                  -> std::shared_ptr<List::list<T1>> { return std::move(acc); },
              [&](const typename List::list<T1>::cons _args)
                  -> std::shared_ptr<List::list<T1>> {
                T1 x = _args._a0;
                std::shared_ptr<List::list<T1>> rest = _args._a1;
                return go(List::list<T1>::ctor::cons_(x, std::move(acc)),
                          std::move(rest));
              }},
          xs->v());
    };
    return go(List::list<T1>::ctor::nil_(), l);
  }

  static std::shared_ptr<List::list<unsigned int>>
  local_flatten(const std::shared_ptr<
                List::list<std::shared_ptr<List::list<unsigned int>>>> &xss);

  static bool local_mem(const unsigned int n,
                        const std::shared_ptr<List::list<unsigned int>> &l);

  template <typename T1>
  static unsigned int local_length(const std::shared_ptr<List::list<T1>> &xs) {
    return std::visit(
        Overloaded{
            [](const typename List::list<T1>::nil _args) -> unsigned int {
              return 0;
            },
            [](const typename List::list<T1>::cons _args) -> unsigned int {
              std::shared_ptr<List::list<T1>> rest = _args._a1;
              return (local_length<T1>(std::move(rest)) + 1);
            }},
        xs->v());
  }

  static inline const unsigned int test_sum =
      local_sum(List::list<unsigned int>::ctor::cons_(
          (0 + 1), List::list<unsigned int>::ctor::cons_(
                       ((0 + 1) + 1),
                       List::list<unsigned int>::ctor::cons_(
                           (((0 + 1) + 1) + 1),
                           List::list<unsigned int>::ctor::cons_(
                               ((((0 + 1) + 1) + 1) + 1),
                               List::list<unsigned int>::ctor::cons_(
                                   (((((0 + 1) + 1) + 1) + 1) + 1),
                                   List::list<unsigned int>::ctor::nil_()))))));

  static inline const std::shared_ptr<List::list<unsigned int>> test_rev =
      local_rev<unsigned int>(List::list<unsigned int>::ctor::cons_(
          (0 + 1),
          List::list<unsigned int>::ctor::cons_(
              ((0 + 1) + 1), List::list<unsigned int>::ctor::cons_(
                                 (((0 + 1) + 1) + 1),
                                 List::list<unsigned int>::ctor::nil_()))));

  static inline const std::shared_ptr<List::list<unsigned int>> test_flatten =
      local_flatten(
          List::list<std::shared_ptr<List::list<unsigned int>>>::ctor::cons_(
              List::list<unsigned int>::ctor::cons_(
                  (0 + 1),
                  List::list<unsigned int>::ctor::cons_(
                      ((0 + 1) + 1), List::list<unsigned int>::ctor::nil_())),
              List::list<std::shared_ptr<List::list<unsigned int>>>::ctor::
                  cons_(
                      List::list<unsigned int>::ctor::cons_(
                          (((0 + 1) + 1) + 1),
                          List::list<unsigned int>::ctor::nil_()),
                      List::list<std::shared_ptr<List::list<unsigned int>>>::
                          ctor::cons_(
                              List::list<unsigned int>::ctor::cons_(
                                  ((((0 + 1) + 1) + 1) + 1),
                                  List::list<unsigned int>::ctor::cons_(
                                      (((((0 + 1) + 1) + 1) + 1) + 1),
                                      List::list<unsigned int>::ctor::cons_(
                                          ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                                          List::list<
                                              unsigned int>::ctor::nil_()))),
                              List::list<std::shared_ptr<
                                  List::list<unsigned int>>>::ctor::nil_()))));

  static inline const bool test_mem_found = local_mem(
      (((0 + 1) + 1) + 1),
      List::list<unsigned int>::ctor::cons_(
          (0 + 1), List::list<unsigned int>::ctor::cons_(
                       ((0 + 1) + 1),
                       List::list<unsigned int>::ctor::cons_(
                           (((0 + 1) + 1) + 1),
                           List::list<unsigned int>::ctor::cons_(
                               ((((0 + 1) + 1) + 1) + 1),
                               List::list<unsigned int>::ctor::nil_())))));

  static inline const bool test_mem_missing = local_mem(
      (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
      List::list<unsigned int>::ctor::cons_(
          (0 + 1), List::list<unsigned int>::ctor::cons_(
                       ((0 + 1) + 1),
                       List::list<unsigned int>::ctor::cons_(
                           (((0 + 1) + 1) + 1),
                           List::list<unsigned int>::ctor::cons_(
                               ((((0 + 1) + 1) + 1) + 1),
                               List::list<unsigned int>::ctor::nil_())))));

  static inline const unsigned int test_length = local_length<
      unsigned int>(List::list<unsigned int>::ctor::cons_(
      ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
      List::list<unsigned int>::ctor::cons_(
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
          List::list<unsigned int>::ctor::cons_(
              ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
               1),
              List::list<unsigned int>::ctor::cons_(
                  ((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) +
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
                   1),
                  List::list<unsigned int>::ctor::nil_())))));
};
