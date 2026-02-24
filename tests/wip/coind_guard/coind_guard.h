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

struct Stream {
  template <typename A> struct stream {
  public:
    struct Cons {
      A _a0;
      std::shared_ptr<Stream::stream<A>> _a1;
    };
    using variant_t = std::variant<Cons>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit stream(Cons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Stream::stream<A>>
      Cons_(A a0, const std::shared_ptr<Stream::stream<A>> &a1) {
        return std::shared_ptr<Stream::stream<A>>(
            new Stream::stream<A>(Cons{a0, a1}));
      }
      static std::unique_ptr<Stream::stream<A>>
      Cons_uptr(A a0, const std::shared_ptr<Stream::stream<A>> &a1) {
        return std::unique_ptr<Stream::stream<A>>(
            new Stream::stream<A>(Cons{a0, a1}));
      }
      static std::shared_ptr<Stream::stream<A>>
      lazy_(std::function<std::shared_ptr<Stream::stream<A>>()> thunk) {
        return std::shared_ptr<Stream::stream<A>>(new Stream::stream<A>(
            std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<Stream::stream<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    A hd() const {
      return std::visit(
          Overloaded{[](const typename Stream::stream<A>::Cons _args) -> auto {
            A x = _args._a0;
            return x;
          }},
          this->v());
    }
    std::shared_ptr<Stream::stream<A>> tl() const {
      return Stream::stream<A>::ctor::lazy_(
          [=](void) -> std::shared_ptr<Stream::stream<A>> {
            return std::visit(
                Overloaded{[](const typename Stream::stream<A>::Cons _args)
                               -> std::shared_ptr<Stream::stream<A>> {
                  std::shared_ptr<Stream::stream<A>> t = _args._a1;
                  return t;
                }},
                this->v());
          });
    }
    template <typename T2, typename T3, MapsTo<T3, A, T2> F0>
    std::shared_ptr<Stream::stream<T3>>
    zipWith(F0 &&f, const std::shared_ptr<Stream::stream<T2>> &s2) const {
      return Stream::stream<T3>::ctor::lazy_(
          [=](void) -> std::shared_ptr<Stream::stream<T3>> {
            return Stream::stream<T3>::ctor::Cons_(
                f(this->hd(), s2->hd()), this->tl()->zipWith(f, s2->tl()));
          });
    }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<Stream::stream<T2>> smap(F0 &&f) const {
      return Stream::stream<T2>::ctor::lazy_(
          [=](void) -> std::shared_ptr<Stream::stream<T2>> {
            return Stream::stream<T2>::ctor::Cons_(f(this->hd()),
                                                   this->tl()->smap(f));
          });
    }
    std::shared_ptr<List::list<A>> take(const unsigned int n) const {
      if (n <= 0) {
        return List::list<A>::ctor::nil_();
      } else {
        unsigned int n_ = n - 1;
        return List::list<A>::ctor::cons_(this->hd(), this->tl()->take(n_));
      }
    }
  };
};

template <typename T1, MapsTo<T1, T1> F0>
std::shared_ptr<Stream::stream<T1>> iterate(F0 &&f, const T1 x) {
  return Stream::stream<T1>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Stream::stream<T1>> {
        return Stream::stream<T1>::ctor::Cons_(x, iterate<T1>(f, f(x)));
      });
}

template <typename T1, typename T2, MapsTo<std::pair<T1, T2>, T2> F0>
std::shared_ptr<Stream::stream<T1>> unfold(F0 &&f, const T2 seed) {
  T1 a = f(seed).first;
  T2 s_ = f(seed).second;
  return Stream::stream<T1>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Stream::stream<T1>> {
        return Stream::stream<T1>::ctor::Cons_(a, unfold<T1, T2>(f, s_));
      });
}

const std::shared_ptr<Stream::stream<unsigned int>> nats =
    iterate<unsigned int>([](axiom x) { return (x + 1); }, 0);

const std::shared_ptr<Stream::stream<unsigned int>> evens =
    nats->smap([](unsigned int n) { return (n * ((0 + 1) + 1)); });

const std::shared_ptr<Stream::stream<unsigned int>> fibs =
    unfold<unsigned int, std::pair<unsigned int, unsigned int>>(
        [](std::pair<unsigned int, unsigned int> pat) {
          unsigned int a = pat.first;
          unsigned int b = pat.second;
          return std::make_pair(a, std::make_pair(b, (a + b)));
        },
        std::make_pair(0, (0 + 1)));

const std::shared_ptr<Stream::stream<unsigned int>> sum_stream = nats->zipWith(
    [](const unsigned int _x0, const unsigned int _x1) { return (_x0 + _x1); },
    evens);

const std::shared_ptr<List::list<unsigned int>> test_nats_5 =
    nats->take((((((0 + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<List::list<unsigned int>> test_evens_5 =
    evens->take((((((0 + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<List::list<unsigned int>> test_fibs_8 =
    fibs->take(((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<List::list<unsigned int>> test_sum_5 =
    sum_stream->take((((((0 + 1) + 1) + 1) + 1) + 1));

const unsigned int test_iterate_hd = nats->hd();
