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

struct Nat {
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<Nat::nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O _v) : v_(std::move(_v)) {}
    explicit nat(S _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Nat::nat> O_() {
        return std::shared_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::shared_ptr<Nat::nat> S_(const std::shared_ptr<Nat::nat> &a0) {
        return std::shared_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
      static std::unique_ptr<Nat::nat> O_uptr() {
        return std::unique_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::unique_ptr<Nat::nat>
      S_uptr(const std::shared_ptr<Nat::nat> &a0) {
        return std::unique_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
  static std::shared_ptr<Nat::nat> add(const std::shared_ptr<Nat::nat> &n,
                                       std::shared_ptr<Nat::nat> m);
};

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  std::shared_ptr<Nat::nat> length() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<Nat::nat> {
              return Nat::nat::ctor::O_();
            },
            [](const typename List<A>::cons _args)
                -> std::shared_ptr<Nat::nat> {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return Nat::nat::ctor::S_(std::move(l_)->length());
            }},
        this->v());
  }
};

struct ListDef {
  template <typename T1>
  static std::shared_ptr<List<T1>> repeat(const T1 x,
                                          const std::shared_ptr<Nat::nat> &n);
};

std::shared_ptr<Nat::nat> foo(std::shared_ptr<Nat::nat> n, const bool b);
template <typename T1>
std::shared_ptr<Nat::nat> _foo_aux(const T1 a,
                                   const std::shared_ptr<Nat::nat> &n) {
  return ListDef::repeat<T1>(a, n)->length();
}

template <typename T1>
std::shared_ptr<List<T1>> ListDef::repeat(const T1 x,
                                          const std::shared_ptr<Nat::nat> &n) {
  return std::visit(
      Overloaded{
          [](const typename Nat::nat::O _args) -> std::shared_ptr<List<T1>> {
            return List<T1>::ctor::nil_();
          },
          [&](const typename Nat::nat::S _args) -> std::shared_ptr<List<T1>> {
            std::shared_ptr<Nat::nat> k = _args._a0;
            return List<T1>::ctor::cons_(x,
                                         ListDef::repeat<T1>(x, std::move(k)));
          }},
      n->v());
}
