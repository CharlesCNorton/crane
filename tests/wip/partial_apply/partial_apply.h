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

struct PartialApply {
  static std::shared_ptr<List::list<unsigned int>>
  inc_all(const std::shared_ptr<List::list<unsigned int>> &l);

  static std::shared_ptr<List::list<std::pair<unsigned int, unsigned int>>>
  tag_all(const std::shared_ptr<List::list<unsigned int>> &l);

  static std::shared_ptr<List::list<std::optional<unsigned int>>>
  wrap_all(const std::shared_ptr<List::list<unsigned int>> &l);

  static std::shared_ptr<List::list<std::function<std::shared_ptr<
      List::list<unsigned int>>(std::shared_ptr<List::list<unsigned int>>)>>>
  prepend_each(const std::shared_ptr<List::list<unsigned int>> &l);

  template <typename A> struct tagged {
  public:
    struct Tag {
      unsigned int _a0;
      A _a1;
    };
    using variant_t = std::variant<Tag>;

  private:
    variant_t v_;
    explicit tagged(Tag _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tagged<A>> Tag_(unsigned int a0, A a1) {
        return std::shared_ptr<tagged<A>>(new tagged<A>(Tag{a0, a1}));
      }
      static std::unique_ptr<tagged<A>> Tag_uptr(unsigned int a0, A a1) {
        return std::unique_ptr<tagged<A>>(new tagged<A>(Tag{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rect(F0 &&f, const std::shared_ptr<tagged<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tagged<T1>::Tag _args) -> T2 {
          unsigned int n = _args._a0;
          T1 a = _args._a1;
          return f(std::move(n), a);
        }},
        t->v());
  }

  template <typename T1, typename T2, MapsTo<T2, unsigned int, T1> F0>
  static T2 tagged_rec(F0 &&f, const std::shared_ptr<tagged<T1>> &t) {
    return std::visit(
        Overloaded{[&](const typename tagged<T1>::Tag _args) -> T2 {
          unsigned int n = _args._a0;
          T1 a = _args._a1;
          return f(std::move(n), a);
        }},
        t->v());
  }

  static std::shared_ptr<List::list<std::shared_ptr<tagged<bool>>>>
  tag_with(const unsigned int n, const std::shared_ptr<List::list<bool>> &l);

  static std::shared_ptr<List::list<
      std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>>
  double_tag(const std::shared_ptr<List::list<unsigned int>> &l);

  static unsigned int
  sum_with_init(const unsigned int init,
                const std::shared_ptr<List::list<unsigned int>> &l);

  static inline const std::shared_ptr<List::list<unsigned int>> test_inc =
      inc_all(List::list<unsigned int>::ctor::cons_(
          (0 + 1),
          List::list<unsigned int>::ctor::cons_(
              ((0 + 1) + 1), List::list<unsigned int>::ctor::cons_(
                                 (((0 + 1) + 1) + 1),
                                 List::list<unsigned int>::ctor::nil_()))));

  static inline const std::shared_ptr<
      List::list<std::pair<unsigned int, unsigned int>>>
      test_tag = tag_all(List::list<unsigned int>::ctor::cons_(
          ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          List::list<unsigned int>::ctor::cons_(
              ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
                  ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
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
                  List::list<unsigned int>::ctor::nil_()))));

  static inline const std::shared_ptr<List::list<std::optional<unsigned int>>>
      test_wrap = wrap_all(List::list<unsigned int>::ctor::cons_(
          (((((0 + 1) + 1) + 1) + 1) + 1),
          List::list<unsigned int>::ctor::cons_(
              ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
              List::list<unsigned int>::ctor::cons_(
                  (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                  List::list<unsigned int>::ctor::nil_()))));

 static inline const std::shared_ptr<List::list<std::shared_ptr<tagged<bool>>>> test_tag_with = tag_with((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List::list<bool>::ctor::cons_(true, List::list<bool>::ctor::cons_(false, List::list<bool>::ctor::cons_(true, List::list<bool>::ctor::nil_()))));

 static inline const unsigned int test_sum = sum_with_init(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List::list<unsigned int>::ctor::cons_((0 + 1), List::list<unsigned int>::ctor::cons_(((0 + 1) + 1), List::list<unsigned int>::ctor::cons_((((0 + 1) + 1) + 1), List::list<unsigned int>::ctor::nil_()))));
};
