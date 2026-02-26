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

struct WhereClause {
  struct expr {
  public:
    struct Num {
      unsigned int _a0;
    };
    struct Plus {
      std::shared_ptr<expr> _a0;
      std::shared_ptr<expr> _a1;
    };
    struct Times {
      std::shared_ptr<expr> _a0;
      std::shared_ptr<expr> _a1;
    };
    using variant_t = std::variant<Num, Plus, Times>;

  private:
    variant_t v_;
    explicit expr(Num _v) : v_(std::move(_v)) {}
    explicit expr(Plus _v) : v_(std::move(_v)) {}
    explicit expr(Times _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<expr> Num_(unsigned int a0) {
        return std::shared_ptr<expr>(new expr(Num{a0}));
      }
      static std::shared_ptr<expr> Plus_(const std::shared_ptr<expr> &a0,
                                         const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(Plus{a0, a1}));
      }
      static std::shared_ptr<expr> Times_(const std::shared_ptr<expr> &a0,
                                          const std::shared_ptr<expr> &a1) {
        return std::shared_ptr<expr>(new expr(Times{a0, a1}));
      }
      static std::unique_ptr<expr> Num_uptr(unsigned int a0) {
        return std::unique_ptr<expr>(new expr(Num{a0}));
      }
      static std::unique_ptr<expr> Plus_uptr(const std::shared_ptr<expr> &a0,
                                             const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(Plus{a0, a1}));
      }
      static std::unique_ptr<expr> Times_uptr(const std::shared_ptr<expr> &a0,
                                              const std::shared_ptr<expr> &a1) {
        return std::unique_ptr<expr>(new expr(Times{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F1,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2>
  static T1 Expr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<expr> &e) {
    return std::visit(Overloaded{[&](const typename expr::Num _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename expr::Plus _args) -> T1 {
                                   std::shared_ptr<expr> e0 = _args._a0;
                                   std::shared_ptr<expr> e1 = _args._a1;
                                   return f0(e0, Expr_rect<T1>(f, f0, f1, e0),
                                             e1, Expr_rect<T1>(f, f0, f1, e1));
                                 },
                                 [&](const typename expr::Times _args) -> T1 {
                                   std::shared_ptr<expr> e0 = _args._a0;
                                   std::shared_ptr<expr> e1 = _args._a1;
                                   return f1(e0, Expr_rect<T1>(f, f0, f1, e0),
                                             e1, Expr_rect<T1>(f, f0, f1, e1));
                                 }},
                      e->v());
  }

  template <typename T1, MapsTo<T1, unsigned int> F0,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F1,
            MapsTo<T1, std::shared_ptr<expr>, T1, std::shared_ptr<expr>, T1> F2>
  static T1 Expr_rec(F0 &&f, F1 &&f0, F2 &&f1, const std::shared_ptr<expr> &e) {
    return std::visit(Overloaded{[&](const typename expr::Num _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename expr::Plus _args) -> T1 {
                                   std::shared_ptr<expr> e0 = _args._a0;
                                   std::shared_ptr<expr> e1 = _args._a1;
                                   return f0(e0, Expr_rec<T1>(f, f0, f1, e0),
                                             e1, Expr_rec<T1>(f, f0, f1, e1));
                                 },
                                 [&](const typename expr::Times _args) -> T1 {
                                   std::shared_ptr<expr> e0 = _args._a0;
                                   std::shared_ptr<expr> e1 = _args._a1;
                                   return f1(e0, Expr_rec<T1>(f, f0, f1, e0),
                                             e1, Expr_rec<T1>(f, f0, f1, e1));
                                 }},
                      e->v());
  }

  static unsigned int eval(const std::shared_ptr<expr> &e);

  static unsigned int expr_size(const std::shared_ptr<expr> &e);

  struct bExpr {
  public:
    struct BTrue {};
    struct BFalse {};
    struct BAnd {
      std::shared_ptr<bExpr> _a0;
      std::shared_ptr<bExpr> _a1;
    };
    struct BOr {
      std::shared_ptr<bExpr> _a0;
      std::shared_ptr<bExpr> _a1;
    };
    struct BNot {
      std::shared_ptr<bExpr> _a0;
    };
    using variant_t = std::variant<BTrue, BFalse, BAnd, BOr, BNot>;

  private:
    variant_t v_;
    explicit bExpr(BTrue _v) : v_(std::move(_v)) {}
    explicit bExpr(BFalse _v) : v_(std::move(_v)) {}
    explicit bExpr(BAnd _v) : v_(std::move(_v)) {}
    explicit bExpr(BOr _v) : v_(std::move(_v)) {}
    explicit bExpr(BNot _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<bExpr> BTrue_() {
        return std::shared_ptr<bExpr>(new bExpr(BTrue{}));
      }
      static std::shared_ptr<bExpr> BFalse_() {
        return std::shared_ptr<bExpr>(new bExpr(BFalse{}));
      }
      static std::shared_ptr<bExpr> BAnd_(const std::shared_ptr<bExpr> &a0,
                                          const std::shared_ptr<bExpr> &a1) {
        return std::shared_ptr<bExpr>(new bExpr(BAnd{a0, a1}));
      }
      static std::shared_ptr<bExpr> BOr_(const std::shared_ptr<bExpr> &a0,
                                         const std::shared_ptr<bExpr> &a1) {
        return std::shared_ptr<bExpr>(new bExpr(BOr{a0, a1}));
      }
      static std::shared_ptr<bExpr> BNot_(const std::shared_ptr<bExpr> &a0) {
        return std::shared_ptr<bExpr>(new bExpr(BNot{a0}));
      }
      static std::unique_ptr<bExpr> BTrue_uptr() {
        return std::unique_ptr<bExpr>(new bExpr(BTrue{}));
      }
      static std::unique_ptr<bExpr> BFalse_uptr() {
        return std::unique_ptr<bExpr>(new bExpr(BFalse{}));
      }
      static std::unique_ptr<bExpr>
      BAnd_uptr(const std::shared_ptr<bExpr> &a0,
                const std::shared_ptr<bExpr> &a1) {
        return std::unique_ptr<bExpr>(new bExpr(BAnd{a0, a1}));
      }
      static std::unique_ptr<bExpr> BOr_uptr(const std::shared_ptr<bExpr> &a0,
                                             const std::shared_ptr<bExpr> &a1) {
        return std::unique_ptr<bExpr>(new bExpr(BOr{a0, a1}));
      }
      static std::unique_ptr<bExpr>
      BNot_uptr(const std::shared_ptr<bExpr> &a0) {
        return std::unique_ptr<bExpr>(new bExpr(BNot{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<bExpr>, T1, std::shared_ptr<bExpr>, T1> F2,
      MapsTo<T1, std::shared_ptr<bExpr>, T1, std::shared_ptr<bExpr>, T1> F3,
      MapsTo<T1, std::shared_ptr<bExpr>, T1> F4>
  static T1 BExpr_rect(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                       const std::shared_ptr<bExpr> &b) {
    return std::visit(
        Overloaded{[&](const typename bExpr::BTrue _args) -> T1 { return f; },
                   [&](const typename bExpr::BFalse _args) -> T1 { return f0; },
                   [&](const typename bExpr::BAnd _args) -> T1 {
                     std::shared_ptr<bExpr> b0 = _args._a0;
                     std::shared_ptr<bExpr> b1 = _args._a1;
                     return f1(b0, BExpr_rect<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename bExpr::BOr _args) -> T1 {
                     std::shared_ptr<bExpr> b0 = _args._a0;
                     std::shared_ptr<bExpr> b1 = _args._a1;
                     return f2(b0, BExpr_rect<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rect<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename bExpr::BNot _args) -> T1 {
                     std::shared_ptr<bExpr> b0 = _args._a0;
                     return f3(b0, BExpr_rect<T1>(f, f0, f1, f2, f3, b0));
                   }},
        b->v());
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<bExpr>, T1, std::shared_ptr<bExpr>, T1> F2,
      MapsTo<T1, std::shared_ptr<bExpr>, T1, std::shared_ptr<bExpr>, T1> F3,
      MapsTo<T1, std::shared_ptr<bExpr>, T1> F4>
  static T1 BExpr_rec(const T1 f, const T1 f0, F2 &&f1, F3 &&f2, F4 &&f3,
                      const std::shared_ptr<bExpr> &b) {
    return std::visit(
        Overloaded{[&](const typename bExpr::BTrue _args) -> T1 { return f; },
                   [&](const typename bExpr::BFalse _args) -> T1 { return f0; },
                   [&](const typename bExpr::BAnd _args) -> T1 {
                     std::shared_ptr<bExpr> b0 = _args._a0;
                     std::shared_ptr<bExpr> b1 = _args._a1;
                     return f1(b0, BExpr_rec<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename bExpr::BOr _args) -> T1 {
                     std::shared_ptr<bExpr> b0 = _args._a0;
                     std::shared_ptr<bExpr> b1 = _args._a1;
                     return f2(b0, BExpr_rec<T1>(f, f0, f1, f2, f3, b0), b1,
                               BExpr_rec<T1>(f, f0, f1, f2, f3, b1));
                   },
                   [&](const typename bExpr::BNot _args) -> T1 {
                     std::shared_ptr<bExpr> b0 = _args._a0;
                     return f3(b0, BExpr_rec<T1>(f, f0, f1, f2, f3, b0));
                   }},
        b->v());
  }

  static bool beval(const std::shared_ptr<bExpr> &e);

  struct aExpr {
  public:
    struct ANum {
      unsigned int _a0;
    };
    struct APlus {
      std::shared_ptr<aExpr> _a0;
      std::shared_ptr<aExpr> _a1;
    };
    struct AIf {
      std::shared_ptr<bExpr> _a0;
      std::shared_ptr<aExpr> _a1;
      std::shared_ptr<aExpr> _a2;
    };
    using variant_t = std::variant<ANum, APlus, AIf>;

  private:
    variant_t v_;
    explicit aExpr(ANum _v) : v_(std::move(_v)) {}
    explicit aExpr(APlus _v) : v_(std::move(_v)) {}
    explicit aExpr(AIf _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<aExpr> ANum_(unsigned int a0) {
        return std::shared_ptr<aExpr>(new aExpr(ANum{a0}));
      }
      static std::shared_ptr<aExpr> APlus_(const std::shared_ptr<aExpr> &a0,
                                           const std::shared_ptr<aExpr> &a1) {
        return std::shared_ptr<aExpr>(new aExpr(APlus{a0, a1}));
      }
      static std::shared_ptr<aExpr> AIf_(const std::shared_ptr<bExpr> &a0,
                                         const std::shared_ptr<aExpr> &a1,
                                         const std::shared_ptr<aExpr> &a2) {
        return std::shared_ptr<aExpr>(new aExpr(AIf{a0, a1, a2}));
      }
      static std::unique_ptr<aExpr> ANum_uptr(unsigned int a0) {
        return std::unique_ptr<aExpr>(new aExpr(ANum{a0}));
      }
      static std::unique_ptr<aExpr>
      APlus_uptr(const std::shared_ptr<aExpr> &a0,
                 const std::shared_ptr<aExpr> &a1) {
        return std::unique_ptr<aExpr>(new aExpr(APlus{a0, a1}));
      }
      static std::unique_ptr<aExpr> AIf_uptr(const std::shared_ptr<bExpr> &a0,
                                             const std::shared_ptr<aExpr> &a1,
                                             const std::shared_ptr<aExpr> &a2) {
        return std::unique_ptr<aExpr>(new aExpr(AIf{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<aExpr>, T1, std::shared_ptr<aExpr>, T1> F1,
      MapsTo<T1, std::shared_ptr<bExpr>, std::shared_ptr<aExpr>, T1,
             std::shared_ptr<aExpr>, T1>
          F2>
  static T1 AExpr_rect(F0 &&f, F1 &&f0, F2 &&f1,
                       const std::shared_ptr<aExpr> &a) {
    return std::visit(Overloaded{[&](const typename aExpr::ANum _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename aExpr::APlus _args) -> T1 {
                                   std::shared_ptr<aExpr> a0 = _args._a0;
                                   std::shared_ptr<aExpr> a1 = _args._a1;
                                   return f0(a0, AExpr_rect<T1>(f, f0, f1, a0),
                                             a1, AExpr_rect<T1>(f, f0, f1, a1));
                                 },
                                 [&](const typename aExpr::AIf _args) -> T1 {
                                   std::shared_ptr<bExpr> b = _args._a0;
                                   std::shared_ptr<aExpr> a0 = _args._a1;
                                   std::shared_ptr<aExpr> a1 = _args._a2;
                                   return f1(std::move(b), a0,
                                             AExpr_rect<T1>(f, f0, f1, a0), a1,
                                             AExpr_rect<T1>(f, f0, f1, a1));
                                 }},
                      a->v());
  }

  template <
      typename T1, MapsTo<T1, unsigned int> F0,
      MapsTo<T1, std::shared_ptr<aExpr>, T1, std::shared_ptr<aExpr>, T1> F1,
      MapsTo<T1, std::shared_ptr<bExpr>, std::shared_ptr<aExpr>, T1,
             std::shared_ptr<aExpr>, T1>
          F2>
  static T1 AExpr_rec(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<aExpr> &a) {
    return std::visit(Overloaded{[&](const typename aExpr::ANum _args) -> T1 {
                                   unsigned int n = _args._a0;
                                   return f(std::move(n));
                                 },
                                 [&](const typename aExpr::APlus _args) -> T1 {
                                   std::shared_ptr<aExpr> a0 = _args._a0;
                                   std::shared_ptr<aExpr> a1 = _args._a1;
                                   return f0(a0, AExpr_rec<T1>(f, f0, f1, a0),
                                             a1, AExpr_rec<T1>(f, f0, f1, a1));
                                 },
                                 [&](const typename aExpr::AIf _args) -> T1 {
                                   std::shared_ptr<bExpr> b = _args._a0;
                                   std::shared_ptr<aExpr> a0 = _args._a1;
                                   std::shared_ptr<aExpr> a1 = _args._a2;
                                   return f1(std::move(b), a0,
                                             AExpr_rec<T1>(f, f0, f1, a0), a1,
                                             AExpr_rec<T1>(f, f0, f1, a1));
                                 }},
                      a->v());
  }

  static unsigned int aeval(const std::shared_ptr<aExpr> &e);

  static inline const unsigned int test_eval_plus =
      eval(expr::ctor::Plus_(expr::ctor::Num_((((0 + 1) + 1) + 1)),
                             expr::ctor::Num_(((((0 + 1) + 1) + 1) + 1))));

  static inline const unsigned int test_eval_times = eval(expr::ctor::Times_(
      expr::ctor::Num_((((((0 + 1) + 1) + 1) + 1) + 1)),
      expr::ctor::Num_(((((((0 + 1) + 1) + 1) + 1) + 1) + 1))));

  static inline const unsigned int test_eval_nested = eval(expr::ctor::Plus_(
      expr::ctor::Times_(expr::ctor::Num_(((0 + 1) + 1)),
                         expr::ctor::Num_((((0 + 1) + 1) + 1))),
      expr::ctor::Num_((0 + 1))));

  static inline const unsigned int test_size = expr_size(expr::ctor::Plus_(
      expr::ctor::Times_(expr::ctor::Num_(((0 + 1) + 1)),
                         expr::ctor::Num_((((0 + 1) + 1) + 1))),
      expr::ctor::Num_((0 + 1))));

  static inline const bool test_beval = beval(bExpr::ctor::BAnd_(
      bExpr::ctor::BTrue_(), bExpr::ctor::BNot_(bExpr::ctor::BFalse_())));

  static inline const unsigned int test_aeval = aeval(aExpr::ctor::AIf_(
      bExpr::ctor::BAnd_(bExpr::ctor::BTrue_(), bExpr::ctor::BTrue_()),
      aExpr::ctor::ANum_(
          ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
      aExpr::ctor::ANum_(
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
           1))));
};
