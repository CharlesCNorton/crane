#include "lazy.h"
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

struct streamA;
struct streamB;
struct StreamA {
  template <typename A> struct streamA {
  public:
    struct consA {
      A _a0;
      std::shared_ptr<StreamB::streamB<A>> _a1;
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
      static std::shared_ptr<StreamA::streamA<A>>
      consA_(A a0, const std::shared_ptr<StreamB::streamB<A>> &a1) {
        return std::shared_ptr<StreamA::streamA<A>>(
            new StreamA::streamA<A>(consA{a0, a1}));
      }
      static std::unique_ptr<StreamA::streamA<A>>
      consA_uptr(A a0, const std::shared_ptr<StreamB::streamB<A>> &a1) {
        return std::unique_ptr<StreamA::streamA<A>>(
            new StreamA::streamA<A>(consA{a0, a1}));
      }
      static std::shared_ptr<StreamA::streamA<A>>
      lazy_(std::function<std::shared_ptr<StreamA::streamA<A>>()> thunk) {
        return std::shared_ptr<StreamA::streamA<A>>(new StreamA::streamA<A>(
            std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<StreamA::streamA<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    A headA() const {
      return std::visit(
          Overloaded{
              [](const typename StreamA::streamA<A>::consA _args) -> auto {
                A x = _args._a0;
                return x;
              }},
          this->v());
    }
    std::shared_ptr<List::list<A>> takeA(const unsigned int fuel) const {
      if (fuel <= 0) {
        return List::list<A>::ctor::nil_();
      } else {
        unsigned int f = fuel - 1;
        return std::visit(
            Overloaded{[&](const typename StreamA::streamA<A>::consA _args)
                           -> std::shared_ptr<List::list<A>> {
              A x = _args._a0;
              std::shared_ptr<StreamB::streamB<A>> t = _args._a1;
              return List::list<A>::ctor::cons_(x, t->takeB(f));
            }},
            this->v());
      }
    }
  };
};
struct StreamB {
  template <typename A> struct streamB {
  public:
    struct consB {
      A _a0;
      std::shared_ptr<StreamA::streamA<A>> _a1;
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
      static std::shared_ptr<StreamB::streamB<A>>
      consB_(A a0, const std::shared_ptr<StreamA::streamA<A>> &a1) {
        return std::shared_ptr<StreamB::streamB<A>>(
            new StreamB::streamB<A>(consB{a0, a1}));
      }
      static std::unique_ptr<StreamB::streamB<A>>
      consB_uptr(A a0, const std::shared_ptr<StreamA::streamA<A>> &a1) {
        return std::unique_ptr<StreamB::streamB<A>>(
            new StreamB::streamB<A>(consB{a0, a1}));
      }
      static std::shared_ptr<StreamB::streamB<A>>
      lazy_(std::function<std::shared_ptr<StreamB::streamB<A>>()> thunk) {
        return std::shared_ptr<StreamB::streamB<A>>(new StreamB::streamB<A>(
            std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<StreamB::streamB<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    A headB() const {
      return std::visit(
          Overloaded{
              [](const typename StreamB::streamB<A>::consB _args) -> auto {
                A x = _args._a0;
                return x;
              }},
          this->v());
    }
    std::shared_ptr<StreamA::streamA<A>> tailB() const {
      return StreamA::streamA<A>::ctor::lazy_(
          [=](void) -> std::shared_ptr<StreamA::streamA<A>> {
            return std::visit(
                Overloaded{[](const typename StreamB::streamB<A>::consB _args)
                               -> std::shared_ptr<StreamA::streamA<A>> {
                  std::shared_ptr<StreamA::streamA<A>> t = _args._a1;
                  return t;
                }},
                this->v());
          });
    }
    std::shared_ptr<List::list<A>> takeB(const unsigned int fuel) const {
      if (fuel <= 0) {
        return List::list<A>::ctor::nil_();
      } else {
        unsigned int f = fuel - 1;
        return std::visit(
            Overloaded{[&](const typename StreamB::streamB<A>::consB _args)
                           -> std::shared_ptr<List::list<A>> {
              A x = _args._a0;
              std::shared_ptr<StreamA::streamA<A>> t = _args._a1;
              return List::list<A>::ctor::cons_(x, t->takeA(f));
            }},
            this->v());
      }
    }
  };
};

std::shared_ptr<StreamA::streamA<unsigned int>> countA(const unsigned int n);
std::shared_ptr<StreamB::streamB<unsigned int>> countB(const unsigned int n);

const unsigned int test_headA = countA(0)->headA();

const unsigned int test_headB =
    countB(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))
        ->headB();

const std::shared_ptr<List::list<unsigned int>> test_take5 =
    countA(0)->takeA((((((0 + 1) + 1) + 1) + 1) + 1));
