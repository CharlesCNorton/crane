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
};

struct DepRecord {
  struct Magma {
  public:
    struct mkMagma {
      std::function<std::any(std::any, std::any)> _a0;
    };
    using variant_t = std::variant<mkMagma>;

  private:
    variant_t v_;
    explicit Magma(mkMagma _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Magma>
      mkMagma_(std::function<std::any(std::any, std::any)> a0) {
        return std::shared_ptr<Magma>(new Magma(mkMagma{a0}));
      }
      static std::unique_ptr<Magma>
      mkMagma_uptr(std::function<std::any(std::any, std::any)> a0) {
        return std::unique_ptr<Magma>(new Magma(mkMagma{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  using carrier = std::any;

  static carrier op(const std::shared_ptr<Magma> &, const carrier,
                    const carrier);

  static inline const std::shared_ptr<Magma> nat_magma =
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      };

  static inline const std::shared_ptr<Magma> bool_magma =
      [](const bool _x0, const bool _x1) { return (_x0 && _x1); };

  struct Monoid {
    std::function<std::any(std::any, std::any)> m_op;
    std::any m_id;
  };

  using m_carrier = std::any;

  static m_carrier m_op(const std::shared_ptr<Monoid> &, const m_carrier,
                        const m_carrier);

  static m_carrier m_id(const std::shared_ptr<Monoid> &m);

  static inline const std::shared_ptr<Monoid> nat_monoid =
      std::make_shared<Monoid>(
          Monoid{[](const unsigned int _x0, const unsigned int _x1) {
                   return (_x0 + _x1);
                 },
                 0});

  static inline const std::shared_ptr<Monoid> nat_mul_monoid =
      std::make_shared<Monoid>(
          Monoid{[](const unsigned int _x0, const unsigned int _x1) {
                   return (_x0 * _x1);
                 },
                 (0 + 1)});

  static m_carrier mfold(const std::shared_ptr<Monoid> &m,
                         const std::shared_ptr<List<std::any>> &l);

  static inline const unsigned int test_fold_add = mfold(
      nat_monoid,
      List<std::any>::ctor::cons_(
          (0 + 1), List<std::any>::ctor::cons_(
                       ((0 + 1) + 1), List<std::any>::ctor::cons_(
                                          (((0 + 1) + 1) + 1),
                                          List<std::any>::ctor::cons_(
                                              ((((0 + 1) + 1) + 1) + 1),
                                              List<std::any>::ctor::nil_())))));

  static inline const unsigned int test_fold_mul = mfold(
      nat_mul_monoid,
      List<std::any>::ctor::cons_(
          ((0 + 1) + 1),
          List<std::any>::ctor::cons_(
              (((0 + 1) + 1) + 1),
              List<std::any>::ctor::cons_(((((0 + 1) + 1) + 1) + 1),
                                          List<std::any>::ctor::nil_()))));

  enum class tag { TNat, TBool };

  template <typename T1>
  static T1 tag_rect(const T1 f, const T1 f0, const tag t) {
    return [&](void) {
      switch (t) {
      case tag::TNat: {
        return f;
      }
      case tag::TBool: {
        return f0;
      }
      }
    }();
  }

  template <typename T1>
  static T1 tag_rec(const T1 f, const T1 f0, const tag t) {
    return [&](void) {
      switch (t) {
      case tag::TNat: {
        return f;
      }
      case tag::TBool: {
        return f0;
      }
      }
    }();
  }

  using tag_type = std::any;

  struct Tagged {
    tag the_tag;
    tag_type the_value;
  };

  static tag the_tag(const std::shared_ptr<Tagged> &t);

  static tag_type the_value(const std::shared_ptr<Tagged> &t);

  static inline const std::shared_ptr<Tagged> tagged_nat =
      std::make_shared<Tagged>(Tagged{
          tag::TNat,
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
           1)});

  static inline const std::shared_ptr<Tagged> tagged_bool =
      std::make_shared<Tagged>(Tagged{tag::TBool, true});
};
