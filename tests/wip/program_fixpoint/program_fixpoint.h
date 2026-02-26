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

struct Sig0 {
  template <typename A> struct sig0 {
  public:
    struct exist {
      A _a0;
    };
    using variant_t = std::variant<exist>;

  private:
    variant_t v_;
    explicit sig0(exist _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Sig0::sig0<A>> exist_(A a0) {
        return std::shared_ptr<Sig0::sig0<A>>(new Sig0::sig0<A>(exist{a0}));
      }
      static std::unique_ptr<Sig0::sig0<A>> exist_uptr(A a0) {
        return std::unique_ptr<Sig0::sig0<A>>(new Sig0::sig0<A>(exist{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

struct SigT {
  template <typename A, typename P> struct sigT {
  public:
    struct existT {
      A _a0;
      P _a1;
    };
    using variant_t = std::variant<existT>;

  private:
    variant_t v_;
    explicit sigT(existT _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<SigT::sigT<A, P>> existT_(A a0, P a1) {
        return std::shared_ptr<SigT::sigT<A, P>>(
            new SigT::sigT<A, P>(existT{a0, a1}));
      }
      static std::unique_ptr<SigT::sigT<A, P>> existT_uptr(A a0, P a1) {
        return std::unique_ptr<SigT::sigT<A, P>>(
            new SigT::sigT<A, P>(existT{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    A projT1() const {
      return std::visit(
          Overloaded{[](const typename SigT::sigT<A, P>::existT _args) -> auto {
            A a = _args._a0;
            return a;
          }},
          this->v());
    }
    P projT2() const {
      return std::visit(
          Overloaded{[](const typename SigT::sigT<A, P>::existT _args) -> auto {
            P h = _args._a1;
            return h;
          }},
          this->v());
    }
  };
};

struct Wf {
  template <
      typename T1, typename T2,
      MapsTo<T2, T1, std::function<T2(std::shared_ptr<Sig0::sig0<T1>>)>> F0>
  static T2 Fix_F_sub(F0 &&f_sub, const T1 x);

  template <
      typename T1, typename T2,
      MapsTo<T2, T1, std::function<T2(std::shared_ptr<Sig0::sig0<T1>>)>> F1>
  static T2 Fix_sub(const T1 _x0, F1 &&_x1);
};

struct ProgFix {
  static std::shared_ptr<List::list<unsigned int>>
  interleave_func(const std::shared_ptr<
                  SigT::sigT<std::shared_ptr<List::list<unsigned int>>,
                             std::shared_ptr<List::list<unsigned int>>>> &);

  static std::shared_ptr<List::list<unsigned int>>
  interleave(std::shared_ptr<List::list<unsigned int>> l1,
             std::shared_ptr<List::list<unsigned int>> l2);

  static inline const std::shared_ptr<List::list<unsigned int>>
      test_interleave = interleave(
          List::list<unsigned int>::ctor::cons_(
              (0 + 1), List::list<unsigned int>::ctor::cons_(
                           (((0 + 1) + 1) + 1),
                           List::list<unsigned int>::ctor::cons_(
                               (((((0 + 1) + 1) + 1) + 1) + 1),
                               List::list<unsigned int>::ctor::nil_()))),
          List::list<unsigned int>::ctor::cons_(
              ((0 + 1) + 1), List::list<unsigned int>::ctor::cons_(
                                 ((((0 + 1) + 1) + 1) + 1),
                                 List::list<unsigned int>::ctor::cons_(
                                     ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                                     List::list<unsigned int>::ctor::nil_()))));
};

template <typename T1, typename T2,
          MapsTo<T2, T1, std::function<T2(std::shared_ptr<Sig0::sig0<T1>>)>> F0>
T2 Wf::Fix_F_sub(F0 &&f_sub, const T1 x) {
  return f_sub(x, [&](axiom x0) { return Wf::Fix_F_sub<T1, T2>(f_sub, x0); });
}

template <typename T1, typename T2,
          MapsTo<T2, T1, std::function<T2(std::shared_ptr<Sig0::sig0<T1>>)>> F1>
T2 Wf::Fix_sub(const T1 _x0, F1 &&_x1) {
  return Wf::Fix_F_sub<T1>(_x0, _x1);
}
