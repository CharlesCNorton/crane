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

struct Expr {
  struct expr {
  public:
    struct Num {
      unsigned int _a0;
    };
    struct Plus {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct Times {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
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
      static std::shared_ptr<Expr::expr> Num_(unsigned int a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(Num{a0}));
      }
      static std::shared_ptr<Expr::expr>
      Plus_(const std::shared_ptr<Expr::expr> &a0,
            const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(Plus{a0, a1}));
      }
      static std::shared_ptr<Expr::expr>
      Times_(const std::shared_ptr<Expr::expr> &a0,
             const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(Times{a0, a1}));
      }
      static std::unique_ptr<Expr::expr> Num_uptr(unsigned int a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(Num{a0}));
      }
      static std::unique_ptr<Expr::expr>
      Plus_uptr(const std::shared_ptr<Expr::expr> &a0,
                const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(Plus{a0, a1}));
      }
      static std::unique_ptr<Expr::expr>
      Times_uptr(const std::shared_ptr<Expr::expr> &a0,
                 const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(Times{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int eval() const {
      return std::visit(
          Overloaded{
              [](const typename Expr::expr::Num _args) -> unsigned int {
                unsigned int n = _args._a0;
                return std::move(n);
              },
              [](const typename Expr::expr::Plus _args) -> unsigned int {
                std::shared_ptr<Expr::expr> a = _args._a0;
                std::shared_ptr<Expr::expr> b = _args._a1;
                return (std::move(a)->eval() + std::move(b)->eval());
              },
              [](const typename Expr::expr::Times _args) -> unsigned int {
                std::shared_ptr<Expr::expr> a = _args._a0;
                std::shared_ptr<Expr::expr> b = _args._a1;
                return (std::move(a)->eval() * std::move(b)->eval());
              }},
          this->v());
    }
    unsigned int expr_size() const {
      return std::visit(
          Overloaded{
              [](const typename Expr::expr::Num _args) -> unsigned int {
                return (0 + 1);
              },
              [](const typename Expr::expr::Plus _args) -> unsigned int {
                std::shared_ptr<Expr::expr> a = _args._a0;
                std::shared_ptr<Expr::expr> b = _args._a1;
                return (((0 + 1) + std::move(a)->expr_size()) +
                        std::move(b)->expr_size());
              },
              [](const typename Expr::expr::Times _args) -> unsigned int {
                std::shared_ptr<Expr::expr> a = _args._a0;
                std::shared_ptr<Expr::expr> b = _args._a1;
                return (((0 + 1) + std::move(a)->expr_size()) +
                        std::move(b)->expr_size());
              }},
          this->v());
    }
  };
};

struct BExpr {
  struct bExpr {
  public:
    struct BTrue {};
    struct BFalse {};
    struct BAnd {
      std::shared_ptr<BExpr::bExpr> _a0;
      std::shared_ptr<BExpr::bExpr> _a1;
    };
    struct BOr {
      std::shared_ptr<BExpr::bExpr> _a0;
      std::shared_ptr<BExpr::bExpr> _a1;
    };
    struct BNot {
      std::shared_ptr<BExpr::bExpr> _a0;
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
      static std::shared_ptr<BExpr::bExpr> BTrue_() {
        return std::shared_ptr<BExpr::bExpr>(new BExpr::bExpr(BTrue{}));
      }
      static std::shared_ptr<BExpr::bExpr> BFalse_() {
        return std::shared_ptr<BExpr::bExpr>(new BExpr::bExpr(BFalse{}));
      }
      static std::shared_ptr<BExpr::bExpr>
      BAnd_(const std::shared_ptr<BExpr::bExpr> &a0,
            const std::shared_ptr<BExpr::bExpr> &a1) {
        return std::shared_ptr<BExpr::bExpr>(new BExpr::bExpr(BAnd{a0, a1}));
      }
      static std::shared_ptr<BExpr::bExpr>
      BOr_(const std::shared_ptr<BExpr::bExpr> &a0,
           const std::shared_ptr<BExpr::bExpr> &a1) {
        return std::shared_ptr<BExpr::bExpr>(new BExpr::bExpr(BOr{a0, a1}));
      }
      static std::shared_ptr<BExpr::bExpr>
      BNot_(const std::shared_ptr<BExpr::bExpr> &a0) {
        return std::shared_ptr<BExpr::bExpr>(new BExpr::bExpr(BNot{a0}));
      }
      static std::unique_ptr<BExpr::bExpr> BTrue_uptr() {
        return std::unique_ptr<BExpr::bExpr>(new BExpr::bExpr(BTrue{}));
      }
      static std::unique_ptr<BExpr::bExpr> BFalse_uptr() {
        return std::unique_ptr<BExpr::bExpr>(new BExpr::bExpr(BFalse{}));
      }
      static std::unique_ptr<BExpr::bExpr>
      BAnd_uptr(const std::shared_ptr<BExpr::bExpr> &a0,
                const std::shared_ptr<BExpr::bExpr> &a1) {
        return std::unique_ptr<BExpr::bExpr>(new BExpr::bExpr(BAnd{a0, a1}));
      }
      static std::unique_ptr<BExpr::bExpr>
      BOr_uptr(const std::shared_ptr<BExpr::bExpr> &a0,
               const std::shared_ptr<BExpr::bExpr> &a1) {
        return std::unique_ptr<BExpr::bExpr>(new BExpr::bExpr(BOr{a0, a1}));
      }
      static std::unique_ptr<BExpr::bExpr>
      BNot_uptr(const std::shared_ptr<BExpr::bExpr> &a0) {
        return std::unique_ptr<BExpr::bExpr>(new BExpr::bExpr(BNot{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    bool beval() const {
      return std::visit(
          Overloaded{[](const typename BExpr::bExpr::BTrue _args) -> bool {
                       return true;
                     },
                     [](const typename BExpr::bExpr::BFalse _args) -> bool {
                       return false;
                     },
                     [](const typename BExpr::bExpr::BAnd _args) -> bool {
                       std::shared_ptr<BExpr::bExpr> a = _args._a0;
                       std::shared_ptr<BExpr::bExpr> b = _args._a1;
                       return (std::move(a)->beval() && std::move(b)->beval());
                     },
                     [](const typename BExpr::bExpr::BOr _args) -> bool {
                       std::shared_ptr<BExpr::bExpr> a = _args._a0;
                       std::shared_ptr<BExpr::bExpr> b = _args._a1;
                       return (std::move(a)->beval() || std::move(b)->beval());
                     },
                     [](const typename BExpr::bExpr::BNot _args) -> bool {
                       std::shared_ptr<BExpr::bExpr> a = _args._a0;
                       return !(std::move(a)->beval());
                     }},
          this->v());
    }
  };
};

struct AExpr {
  struct aExpr {
  public:
    struct ANum {
      unsigned int _a0;
    };
    struct APlus {
      std::shared_ptr<AExpr::aExpr> _a0;
      std::shared_ptr<AExpr::aExpr> _a1;
    };
    struct AIf {
      std::shared_ptr<BExpr::bExpr> _a0;
      std::shared_ptr<AExpr::aExpr> _a1;
      std::shared_ptr<AExpr::aExpr> _a2;
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
      static std::shared_ptr<AExpr::aExpr> ANum_(unsigned int a0) {
        return std::shared_ptr<AExpr::aExpr>(new AExpr::aExpr(ANum{a0}));
      }
      static std::shared_ptr<AExpr::aExpr>
      APlus_(const std::shared_ptr<AExpr::aExpr> &a0,
             const std::shared_ptr<AExpr::aExpr> &a1) {
        return std::shared_ptr<AExpr::aExpr>(new AExpr::aExpr(APlus{a0, a1}));
      }
      static std::shared_ptr<AExpr::aExpr>
      AIf_(const std::shared_ptr<BExpr::bExpr> &a0,
           const std::shared_ptr<AExpr::aExpr> &a1,
           const std::shared_ptr<AExpr::aExpr> &a2) {
        return std::shared_ptr<AExpr::aExpr>(new AExpr::aExpr(AIf{a0, a1, a2}));
      }
      static std::unique_ptr<AExpr::aExpr> ANum_uptr(unsigned int a0) {
        return std::unique_ptr<AExpr::aExpr>(new AExpr::aExpr(ANum{a0}));
      }
      static std::unique_ptr<AExpr::aExpr>
      APlus_uptr(const std::shared_ptr<AExpr::aExpr> &a0,
                 const std::shared_ptr<AExpr::aExpr> &a1) {
        return std::unique_ptr<AExpr::aExpr>(new AExpr::aExpr(APlus{a0, a1}));
      }
      static std::unique_ptr<AExpr::aExpr>
      AIf_uptr(const std::shared_ptr<BExpr::bExpr> &a0,
               const std::shared_ptr<AExpr::aExpr> &a1,
               const std::shared_ptr<AExpr::aExpr> &a2) {
        return std::unique_ptr<AExpr::aExpr>(new AExpr::aExpr(AIf{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int aeval() const {
      return std::visit(
          Overloaded{
              [](const typename AExpr::aExpr::ANum _args) -> unsigned int {
                unsigned int n = _args._a0;
                return std::move(n);
              },
              [](const typename AExpr::aExpr::APlus _args) -> unsigned int {
                std::shared_ptr<AExpr::aExpr> a = _args._a0;
                std::shared_ptr<AExpr::aExpr> b = _args._a1;
                return (std::move(a)->aeval() + std::move(b)->aeval());
              },
              [](const typename AExpr::aExpr::AIf _args) -> unsigned int {
                std::shared_ptr<BExpr::bExpr> c = _args._a0;
                std::shared_ptr<AExpr::aExpr> t = _args._a1;
                std::shared_ptr<AExpr::aExpr> f = _args._a2;
                if (c->beval()) {
                  return std::move(t)->aeval();
                } else {
                  return std::move(f)->aeval();
                }
              }},
          this->v());
    }
  };
};

const unsigned int test_eval_plus =
    Expr::expr::ctor::Plus_(Expr::expr::ctor::Num_((((0 + 1) + 1) + 1)),
                            Expr::expr::ctor::Num_(((((0 + 1) + 1) + 1) + 1)))
        ->eval();

const unsigned int test_eval_times =
    Expr::expr::ctor::Times_(
        Expr::expr::ctor::Num_((((((0 + 1) + 1) + 1) + 1) + 1)),
        Expr::expr::ctor::Num_(((((((0 + 1) + 1) + 1) + 1) + 1) + 1)))
        ->eval();

const unsigned int test_eval_nested =
    Expr::expr::ctor::Plus_(
        Expr::expr::ctor::Times_(Expr::expr::ctor::Num_(((0 + 1) + 1)),
                                 Expr::expr::ctor::Num_((((0 + 1) + 1) + 1))),
        Expr::expr::ctor::Num_((0 + 1)))
        ->eval();

const unsigned int test_size =
    Expr::expr::ctor::Plus_(
        Expr::expr::ctor::Times_(Expr::expr::ctor::Num_(((0 + 1) + 1)),
                                 Expr::expr::ctor::Num_((((0 + 1) + 1) + 1))),
        Expr::expr::ctor::Num_((0 + 1)))
        ->expr_size();

const bool test_beval =
    BExpr::bExpr::ctor::BAnd_(
        BExpr::bExpr::ctor::BTrue_(),
        BExpr::bExpr::ctor::BNot_(BExpr::bExpr::ctor::BFalse_()))
        ->beval();

const unsigned int test_aeval =
    AExpr::aExpr::ctor::AIf_(
        BExpr::bExpr::ctor::BAnd_(BExpr::bExpr::ctor::BTrue_(),
                                  BExpr::bExpr::ctor::BTrue_()),
        AExpr::aExpr::ctor::ANum_(
            ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)),
        AExpr::aExpr::ctor::ANum_(
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
             1)))
        ->aeval();
