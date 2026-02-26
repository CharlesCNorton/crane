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
    unsigned int length() const {
      return std::visit(
          Overloaded{
              [](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (std::move(l_)->length() + 1);
              }},
          this->v());
    }
  };
};

struct Compare_dec {
  static bool le_lt_dec(const unsigned int n, const unsigned int m);
};

struct MergeSort {
  static std::pair<std::shared_ptr<List::list<unsigned int>>,
                   std::shared_ptr<List::list<unsigned int>>>
  split(const std::shared_ptr<List::list<unsigned int>> &l);

  static std::shared_ptr<List::list<unsigned int>>
  merge(std::shared_ptr<List::list<unsigned int>> l1,
        const std::shared_ptr<List::list<unsigned int>> &l2);

  static std::shared_ptr<List::list<unsigned int>>
  msort_go(const unsigned int fuel,
           std::shared_ptr<List::list<unsigned int>> l);

  static std::shared_ptr<List::list<unsigned int>>
  msort(const std::shared_ptr<List::list<unsigned int>> &l);
};

bool le_lt_dec(const unsigned int n, const unsigned int m);
