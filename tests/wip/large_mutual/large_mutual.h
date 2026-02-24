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

struct stmt;
struct expr;
struct bexpr;
struct Stmt {
  struct stmt {
  public:
    struct SAssign {
      unsigned int _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct SSeq {
      std::shared_ptr<Stmt::stmt> _a0;
      std::shared_ptr<Stmt::stmt> _a1;
    };
    struct SIf {
      std::shared_ptr<Bexpr::bexpr> _a0;
      std::shared_ptr<Stmt::stmt> _a1;
      std::shared_ptr<Stmt::stmt> _a2;
    };
    struct SWhile {
      std::shared_ptr<Bexpr::bexpr> _a0;
      std::shared_ptr<Stmt::stmt> _a1;
    };
    struct SSkip {};
    using variant_t = std::variant<SAssign, SSeq, SIf, SWhile, SSkip>;

  private:
    variant_t v_;
    explicit stmt(SAssign _v) : v_(std::move(_v)) {}
    explicit stmt(SSeq _v) : v_(std::move(_v)) {}
    explicit stmt(SIf _v) : v_(std::move(_v)) {}
    explicit stmt(SWhile _v) : v_(std::move(_v)) {}
    explicit stmt(SSkip _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Stmt::stmt>
      SAssign_(unsigned int a0, const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Stmt::stmt>(new Stmt::stmt(SAssign{a0, a1}));
      }
      static std::shared_ptr<Stmt::stmt>
      SSeq_(const std::shared_ptr<Stmt::stmt> &a0,
            const std::shared_ptr<Stmt::stmt> &a1) {
        return std::shared_ptr<Stmt::stmt>(new Stmt::stmt(SSeq{a0, a1}));
      }
      static std::shared_ptr<Stmt::stmt>
      SIf_(const std::shared_ptr<Bexpr::bexpr> &a0,
           const std::shared_ptr<Stmt::stmt> &a1,
           const std::shared_ptr<Stmt::stmt> &a2) {
        return std::shared_ptr<Stmt::stmt>(new Stmt::stmt(SIf{a0, a1, a2}));
      }
      static std::shared_ptr<Stmt::stmt>
      SWhile_(const std::shared_ptr<Bexpr::bexpr> &a0,
              const std::shared_ptr<Stmt::stmt> &a1) {
        return std::shared_ptr<Stmt::stmt>(new Stmt::stmt(SWhile{a0, a1}));
      }
      static std::shared_ptr<Stmt::stmt> SSkip_() {
        return std::shared_ptr<Stmt::stmt>(new Stmt::stmt(SSkip{}));
      }
      static std::unique_ptr<Stmt::stmt>
      SAssign_uptr(unsigned int a0, const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Stmt::stmt>(new Stmt::stmt(SAssign{a0, a1}));
      }
      static std::unique_ptr<Stmt::stmt>
      SSeq_uptr(const std::shared_ptr<Stmt::stmt> &a0,
                const std::shared_ptr<Stmt::stmt> &a1) {
        return std::unique_ptr<Stmt::stmt>(new Stmt::stmt(SSeq{a0, a1}));
      }
      static std::unique_ptr<Stmt::stmt>
      SIf_uptr(const std::shared_ptr<Bexpr::bexpr> &a0,
               const std::shared_ptr<Stmt::stmt> &a1,
               const std::shared_ptr<Stmt::stmt> &a2) {
        return std::unique_ptr<Stmt::stmt>(new Stmt::stmt(SIf{a0, a1, a2}));
      }
      static std::unique_ptr<Stmt::stmt>
      SWhile_uptr(const std::shared_ptr<Bexpr::bexpr> &a0,
                  const std::shared_ptr<Stmt::stmt> &a1) {
        return std::unique_ptr<Stmt::stmt>(new Stmt::stmt(SWhile{a0, a1}));
      }
      static std::unique_ptr<Stmt::stmt> SSkip_uptr() {
        return std::unique_ptr<Stmt::stmt>(new Stmt::stmt(SSkip{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int stmt_size() const {
      return std::visit(
          Overloaded{
              [](const typename Stmt::stmt::SAssign _args) -> unsigned int {
                std::shared_ptr<Expr::expr> e = _args._a1;
                return (std::move(e)->expr_size() + 1);
              },
              [](const typename Stmt::stmt::SSeq _args) -> unsigned int {
                std::shared_ptr<Stmt::stmt> s1 = _args._a0;
                std::shared_ptr<Stmt::stmt> s2 = _args._a1;
                return (
                    (std::move(s1)->stmt_size() + std::move(s2)->stmt_size()) +
                    1);
              },
              [](const typename Stmt::stmt::SIf _args) -> unsigned int {
                std::shared_ptr<Bexpr::bexpr> b = _args._a0;
                std::shared_ptr<Stmt::stmt> s1 = _args._a1;
                std::shared_ptr<Stmt::stmt> s2 = _args._a2;
                return (
                    ((std::move(b)->bexpr_size() + std::move(s1)->stmt_size()) +
                     std::move(s2)->stmt_size()) +
                    1);
              },
              [](const typename Stmt::stmt::SWhile _args) -> unsigned int {
                std::shared_ptr<Bexpr::bexpr> b = _args._a0;
                std::shared_ptr<Stmt::stmt> body = _args._a1;
                return ((std::move(b)->bexpr_size() +
                         std::move(body)->stmt_size()) +
                        1);
              },
              [](const typename Stmt::stmt::SSkip _args) -> unsigned int {
                return (0 + 1);
              }},
          this->v());
    }
  };
};
struct Expr {
  struct expr {
  public:
    struct ENum {
      unsigned int _a0;
    };
    struct EVar {
      unsigned int _a0;
    };
    struct EAdd {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct EMul {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct ECond {
      std::shared_ptr<Bexpr::bexpr> _a0;
      std::shared_ptr<Expr::expr> _a1;
      std::shared_ptr<Expr::expr> _a2;
    };
    using variant_t = std::variant<ENum, EVar, EAdd, EMul, ECond>;

  private:
    variant_t v_;
    explicit expr(ENum _v) : v_(std::move(_v)) {}
    explicit expr(EVar _v) : v_(std::move(_v)) {}
    explicit expr(EAdd _v) : v_(std::move(_v)) {}
    explicit expr(EMul _v) : v_(std::move(_v)) {}
    explicit expr(ECond _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Expr::expr> ENum_(unsigned int a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(ENum{a0}));
      }
      static std::shared_ptr<Expr::expr> EVar_(unsigned int a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EVar{a0}));
      }
      static std::shared_ptr<Expr::expr>
      EAdd_(const std::shared_ptr<Expr::expr> &a0,
            const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EAdd{a0, a1}));
      }
      static std::shared_ptr<Expr::expr>
      EMul_(const std::shared_ptr<Expr::expr> &a0,
            const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(EMul{a0, a1}));
      }
      static std::shared_ptr<Expr::expr>
      ECond_(const std::shared_ptr<Bexpr::bexpr> &a0,
             const std::shared_ptr<Expr::expr> &a1,
             const std::shared_ptr<Expr::expr> &a2) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(ECond{a0, a1, a2}));
      }
      static std::unique_ptr<Expr::expr> ENum_uptr(unsigned int a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(ENum{a0}));
      }
      static std::unique_ptr<Expr::expr> EVar_uptr(unsigned int a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EVar{a0}));
      }
      static std::unique_ptr<Expr::expr>
      EAdd_uptr(const std::shared_ptr<Expr::expr> &a0,
                const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EAdd{a0, a1}));
      }
      static std::unique_ptr<Expr::expr>
      EMul_uptr(const std::shared_ptr<Expr::expr> &a0,
                const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(EMul{a0, a1}));
      }
      static std::unique_ptr<Expr::expr>
      ECond_uptr(const std::shared_ptr<Bexpr::bexpr> &a0,
                 const std::shared_ptr<Expr::expr> &a1,
                 const std::shared_ptr<Expr::expr> &a2) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(ECond{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int expr_size() const {
      return std::visit(
          Overloaded{
              [](const typename Expr::expr::ENum _args) -> unsigned int {
                return (0 + 1);
              },
              [](const typename Expr::expr::EVar _args) -> unsigned int {
                return (0 + 1);
              },
              [](const typename Expr::expr::EAdd _args) -> unsigned int {
                std::shared_ptr<Expr::expr> l = _args._a0;
                std::shared_ptr<Expr::expr> r = _args._a1;
                return (
                    (std::move(l)->expr_size() + std::move(r)->expr_size()) +
                    1);
              },
              [](const typename Expr::expr::EMul _args) -> unsigned int {
                std::shared_ptr<Expr::expr> l = _args._a0;
                std::shared_ptr<Expr::expr> r = _args._a1;
                return (
                    (std::move(l)->expr_size() + std::move(r)->expr_size()) +
                    1);
              },
              [](const typename Expr::expr::ECond _args) -> unsigned int {
                std::shared_ptr<Bexpr::bexpr> b = _args._a0;
                std::shared_ptr<Expr::expr> t = _args._a1;
                std::shared_ptr<Expr::expr> f = _args._a2;
                return (
                    ((std::move(b)->bexpr_size() + std::move(t)->expr_size()) +
                     std::move(f)->expr_size()) +
                    1);
              }},
          this->v());
    }
  };
};
struct Bexpr {
  struct bexpr {
  public:
    struct BTrue {};
    struct BFalse {};
    struct BEq {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct BLt {
      std::shared_ptr<Expr::expr> _a0;
      std::shared_ptr<Expr::expr> _a1;
    };
    struct BAnd {
      std::shared_ptr<Bexpr::bexpr> _a0;
      std::shared_ptr<Bexpr::bexpr> _a1;
    };
    struct BOr {
      std::shared_ptr<Bexpr::bexpr> _a0;
      std::shared_ptr<Bexpr::bexpr> _a1;
    };
    struct BNot {
      std::shared_ptr<Bexpr::bexpr> _a0;
    };
    using variant_t = std::variant<BTrue, BFalse, BEq, BLt, BAnd, BOr, BNot>;

  private:
    variant_t v_;
    explicit bexpr(BTrue _v) : v_(std::move(_v)) {}
    explicit bexpr(BFalse _v) : v_(std::move(_v)) {}
    explicit bexpr(BEq _v) : v_(std::move(_v)) {}
    explicit bexpr(BLt _v) : v_(std::move(_v)) {}
    explicit bexpr(BAnd _v) : v_(std::move(_v)) {}
    explicit bexpr(BOr _v) : v_(std::move(_v)) {}
    explicit bexpr(BNot _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Bexpr::bexpr> BTrue_() {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BTrue{}));
      }
      static std::shared_ptr<Bexpr::bexpr> BFalse_() {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BFalse{}));
      }
      static std::shared_ptr<Bexpr::bexpr>
      BEq_(const std::shared_ptr<Expr::expr> &a0,
           const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BEq{a0, a1}));
      }
      static std::shared_ptr<Bexpr::bexpr>
      BLt_(const std::shared_ptr<Expr::expr> &a0,
           const std::shared_ptr<Expr::expr> &a1) {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BLt{a0, a1}));
      }
      static std::shared_ptr<Bexpr::bexpr>
      BAnd_(const std::shared_ptr<Bexpr::bexpr> &a0,
            const std::shared_ptr<Bexpr::bexpr> &a1) {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BAnd{a0, a1}));
      }
      static std::shared_ptr<Bexpr::bexpr>
      BOr_(const std::shared_ptr<Bexpr::bexpr> &a0,
           const std::shared_ptr<Bexpr::bexpr> &a1) {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BOr{a0, a1}));
      }
      static std::shared_ptr<Bexpr::bexpr>
      BNot_(const std::shared_ptr<Bexpr::bexpr> &a0) {
        return std::shared_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BNot{a0}));
      }
      static std::unique_ptr<Bexpr::bexpr> BTrue_uptr() {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BTrue{}));
      }
      static std::unique_ptr<Bexpr::bexpr> BFalse_uptr() {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BFalse{}));
      }
      static std::unique_ptr<Bexpr::bexpr>
      BEq_uptr(const std::shared_ptr<Expr::expr> &a0,
               const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BEq{a0, a1}));
      }
      static std::unique_ptr<Bexpr::bexpr>
      BLt_uptr(const std::shared_ptr<Expr::expr> &a0,
               const std::shared_ptr<Expr::expr> &a1) {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BLt{a0, a1}));
      }
      static std::unique_ptr<Bexpr::bexpr>
      BAnd_uptr(const std::shared_ptr<Bexpr::bexpr> &a0,
                const std::shared_ptr<Bexpr::bexpr> &a1) {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BAnd{a0, a1}));
      }
      static std::unique_ptr<Bexpr::bexpr>
      BOr_uptr(const std::shared_ptr<Bexpr::bexpr> &a0,
               const std::shared_ptr<Bexpr::bexpr> &a1) {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BOr{a0, a1}));
      }
      static std::unique_ptr<Bexpr::bexpr>
      BNot_uptr(const std::shared_ptr<Bexpr::bexpr> &a0) {
        return std::unique_ptr<Bexpr::bexpr>(new Bexpr::bexpr(BNot{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int bexpr_size() const {
      return std::visit(
          Overloaded{
              [](const typename Bexpr::bexpr::BTrue _args) -> unsigned int {
                return (0 + 1);
              },
              [](const typename Bexpr::bexpr::BFalse _args) -> unsigned int {
                return (0 + 1);
              },
              [](const typename Bexpr::bexpr::BEq _args) -> unsigned int {
                std::shared_ptr<Expr::expr> l = _args._a0;
                std::shared_ptr<Expr::expr> r = _args._a1;
                return (
                    (std::move(l)->expr_size() + std::move(r)->expr_size()) +
                    1);
              },
              [](const typename Bexpr::bexpr::BLt _args) -> unsigned int {
                std::shared_ptr<Expr::expr> l = _args._a0;
                std::shared_ptr<Expr::expr> r = _args._a1;
                return (
                    (std::move(l)->expr_size() + std::move(r)->expr_size()) +
                    1);
              },
              [](const typename Bexpr::bexpr::BAnd _args) -> unsigned int {
                std::shared_ptr<Bexpr::bexpr> l = _args._a0;
                std::shared_ptr<Bexpr::bexpr> r = _args._a1;
                return (
                    (std::move(l)->bexpr_size() + std::move(r)->bexpr_size()) +
                    1);
              },
              [](const typename Bexpr::bexpr::BOr _args) -> unsigned int {
                std::shared_ptr<Bexpr::bexpr> l = _args._a0;
                std::shared_ptr<Bexpr::bexpr> r = _args._a1;
                return (
                    (std::move(l)->bexpr_size() + std::move(r)->bexpr_size()) +
                    1);
              },
              [](const typename Bexpr::bexpr::BNot _args) -> unsigned int {
                std::shared_ptr<Bexpr::bexpr> b0 = _args._a0;
                return (std::move(b0)->bexpr_size() + 1);
              }},
          this->v());
    }
  };
};

const std::shared_ptr<Expr::expr> test_expr = Expr::expr::ctor::EAdd_(
    Expr::expr::ctor::ENum_((0 + 1)),
    Expr::expr::ctor::EMul_(Expr::expr::ctor::ENum_(((0 + 1) + 1)),
                            Expr::expr::ctor::ENum_((((0 + 1) + 1) + 1))));

const std::shared_ptr<Bexpr::bexpr> test_bexpr = Bexpr::bexpr::ctor::BAnd_(
    Bexpr::bexpr::ctor::BEq_(
        Expr::expr::ctor::EVar_(0),
        Expr::expr::ctor::ENum_((((((0 + 1) + 1) + 1) + 1) + 1))),
    Bexpr::bexpr::ctor::BLt_(
        Expr::expr::ctor::EVar_((0 + 1)),
        Expr::expr::ctor::ENum_(
            ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))));

const std::shared_ptr<Stmt::stmt> test_stmt = Stmt::stmt::ctor::SSeq_(
    Stmt::stmt::ctor::SAssign_(
        0, Expr::expr::ctor::ENum_(
               ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) +
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
                 1) +
                1))),
    Stmt::stmt::ctor::SIf_(
        Bexpr::bexpr::ctor::BEq_(
            Expr::expr::ctor::EVar_(0),
            Expr::expr::ctor::ENum_((
                (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) +
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
                 1) +
                1))),
        Stmt::stmt::ctor::SSkip_(),
        Stmt::stmt::ctor::SAssign_(0, Expr::expr::ctor::ENum_(0))));

const unsigned int test_expr_size = test_expr->expr_size();

const unsigned int test_bexpr_size = test_bexpr->bexpr_size();

const unsigned int test_stmt_size = test_stmt->stmt_size();
