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

struct Magma {
  struct magma {
  public:
    struct mkMagma {
      std::function<std::any(std::any, std::any)> _a0;
    };
    using variant_t = std::variant<mkMagma>;

  private:
    variant_t v_;
    explicit magma(mkMagma _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Magma::magma>
      mkMagma_(std::function<std::any(std::any, std::any)> a0) {
        return std::shared_ptr<Magma::magma>(new Magma::magma(mkMagma{a0}));
      }
      static std::unique_ptr<Magma::magma>
      mkMagma_uptr(std::function<std::any(std::any, std::any)> a0) {
        return std::unique_ptr<Magma::magma>(new Magma::magma(mkMagma{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

const std::shared_ptr<Magma::magma> nat_magma =
    [](const unsigned int _x0, const unsigned int _x1) { return (_x0 + _x1); };

const std::shared_ptr<Magma::magma> bool_magma =
    [](const bool _x0, const bool _x1) { return (_x0 && _x1); };

struct Monoid {
  std::function<std::any(std::any, std::any)> m_op;
  std::any m_id;
};

using m_carrier = std::any;

const std::shared_ptr<Monoid> nat_monoid = std::make_shared<Monoid>(Monoid{
    [](const unsigned int _x0, const unsigned int _x1) { return (_x0 + _x1); },
    0});

const std::shared_ptr<Monoid> nat_mul_monoid = std::make_shared<Monoid>(Monoid{
    [](const unsigned int _x0, const unsigned int _x1) { return (_x0 * _x1); },
    (0 + 1)});

const unsigned int test_fold_add =
    nat_monoid->mfold(List::list<std::any>::ctor::cons_(
        (0 + 1),
        List::list<std::any>::ctor::cons_(
            ((0 + 1) + 1), List::list<std::any>::ctor::cons_(
                               (((0 + 1) + 1) + 1),
                               List::list<std::any>::ctor::cons_(
                                   ((((0 + 1) + 1) + 1) + 1),
                                   List::list<std::any>::ctor::nil_())))));

const unsigned int test_fold_mul =
    nat_mul_monoid->mfold(List::list<std::any>::ctor::cons_(
        ((0 + 1) + 1),
        List::list<std::any>::ctor::cons_(
            (((0 + 1) + 1) + 1), List::list<std::any>::ctor::cons_(
                                     ((((0 + 1) + 1) + 1) + 1),
                                     List::list<std::any>::ctor::nil_()))));

enum class tag { TNat, TBool };

using tag_type = std::any;

struct Tagged {
  tag the_tag;
  tag_type the_value;
};

const std::shared_ptr<Tagged> tagged_nat = std::make_shared<Tagged>(Tagged{
    tag::TNat,
    ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
     1)});

const std::shared_ptr<Tagged> tagged_bool =
    std::make_shared<Tagged>(Tagged{tag::TBool, true});
