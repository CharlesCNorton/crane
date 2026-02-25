#include "lazy.h"
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

struct MutualCoind {
  struct streamA;
  struct streamB;
  template <typename A> struct streamA {
  public:
    struct consA {
      A _a0;
      std::shared_ptr<streamB<A>> _a1;
    };
    using variant_t = std::variant<consA>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit streamA(consA _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit streamA(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<streamA<A>>
      consA_(A a0, const std::shared_ptr<streamB<A>> &a1) {
        return std::shared_ptr<streamA<A>>(new streamA<A>(consA{a0, a1}));
      }
      static std::unique_ptr<streamA<A>>
      consA_uptr(A a0, const std::shared_ptr<streamB<A>> &a1) {
        return std::unique_ptr<streamA<A>>(new streamA<A>(consA{a0, a1}));
      }
      static std::shared_ptr<streamA<A>>
      lazy_(std::function<std::shared_ptr<streamA<A>>()> thunk) {
        return std::shared_ptr<streamA<A>>(
            new streamA<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<streamA<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
  };
  template <typename A> struct streamB {
  public:
    struct consB {
      A _a0;
      std::shared_ptr<streamA<A>> _a1;
    };
    using variant_t = std::variant<consB>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit streamB(consB _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit streamB(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<streamB<A>>
      consB_(A a0, const std::shared_ptr<streamA<A>> &a1) {
        return std::shared_ptr<streamB<A>>(new streamB<A>(consB{a0, a1}));
      }
      static std::unique_ptr<streamB<A>>
      consB_uptr(A a0, const std::shared_ptr<streamA<A>> &a1) {
        return std::unique_ptr<streamB<A>>(new streamB<A>(consB{a0, a1}));
      }
      static std::shared_ptr<streamB<A>>
      lazy_(std::function<std::shared_ptr<streamB<A>>()> thunk) {
        return std::shared_ptr<streamB<A>>(
            new streamB<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<streamB<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
  };

  template <typename T1>
  static T1 headA(const std::shared_ptr<streamA<T1>> &s) {
    return std::visit(
        Overloaded{[](const typename streamA<T1>::consA _args) -> T1 {
          T1 x = _args._a0;
          return x;
        }},
        s->v());
  }

  template <typename T1>
  static std::shared_ptr<streamB<T1>>
  tailA(const std::shared_ptr<streamA<T1>> &s) {
    return streamB<T1>::ctor::lazy_([=](void) -> std::shared_ptr<streamB<T1>> {
      return std::visit(Overloaded{[](const typename streamA<T1>::consA _args)
                                       -> std::shared_ptr<streamB<T1>> {
                          std::shared_ptr<streamB<T1>> t = _args._a1;
                          return t;
                        }},
                        s->v());
    });
  }

  template <typename T1>
  static T1 headB(const std::shared_ptr<streamB<T1>> &s) {
    return std::visit(
        Overloaded{[](const typename streamB<T1>::consB _args) -> T1 {
          T1 x = _args._a0;
          return x;
        }},
        s->v());
  }

  template <typename T1>
  static std::shared_ptr<streamA<T1>>
  tailB(const std::shared_ptr<streamB<T1>> &s) {
    return streamA<T1>::ctor::lazy_([=](void) -> std::shared_ptr<streamA<T1>> {
      return std::visit(Overloaded{[](const typename streamB<T1>::consB _args)
                                       -> std::shared_ptr<streamA<T1>> {
                          std::shared_ptr<streamA<T1>> t = _args._a1;
                          return t;
                        }},
                        s->v());
    });
  }

  static std::shared_ptr<streamA<unsigned int>> countA(const unsigned int n);
  static std::shared_ptr<streamB<unsigned int>> countB(const unsigned int n);

  template <typename T1>
  static std::shared_ptr<List::list<T1>>
  takeA(const unsigned int fuel, const std::shared_ptr<streamA<T1>> &s) {
    if (fuel <= 0) {
      return List::list<T1>::ctor::nil_();
    } else {
      unsigned int f = fuel - 1;
      return std::visit(Overloaded{[&](const typename streamA<T1>::consA _args)
                                       -> std::shared_ptr<List::list<T1>> {
                          T1 x = _args._a0;
                          std::shared_ptr<streamB<T1>> t = _args._a1;
                          return List::list<T1>::ctor::cons_(x,
                                                             takeB<T1>(f, t));
                        }},
                        s->v());
    }
  }
  template <typename T1>
  static std::shared_ptr<List::list<T1>>
  takeB(const unsigned int fuel, const std::shared_ptr<streamB<T1>> &s) {
    if (fuel <= 0) {
      return List::list<T1>::ctor::nil_();
    } else {
      unsigned int f = fuel - 1;
      return std::visit(Overloaded{[&](const typename streamB<T1>::consB _args)
                                       -> std::shared_ptr<List::list<T1>> {
                          T1 x = _args._a0;
                          std::shared_ptr<streamA<T1>> t = _args._a1;
                          return List::list<T1>::ctor::cons_(x,
                                                             takeA<T1>(f, t));
                        }},
                        s->v());
    }
  }

  static inline const unsigned int test_headA = headA<unsigned int>(countA(0));

  static inline const unsigned int test_headB = headB<unsigned int>(
      countB(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)));

  static inline const std::shared_ptr<List::list<unsigned int>> test_take5 =
      takeA<unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1), countA(0));
};
