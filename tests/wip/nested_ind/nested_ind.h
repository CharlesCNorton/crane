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
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a,
                                                         std::move(l1)->app(m));
                     }},
          this->v());
    }
  };
};

struct Expr {
  struct expr {
  public:
    struct Lit {
      unsigned int _a0;
    };
    struct Add {
      std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> _a0;
    };
    struct Mul {
      std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> _a0;
    };
    using variant_t = std::variant<Lit, Add, Mul>;

  private:
    variant_t v_;
    explicit expr(Lit _v) : v_(std::move(_v)) {}
    explicit expr(Add _v) : v_(std::move(_v)) {}
    explicit expr(Mul _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Expr::expr> Lit_(unsigned int a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(Lit{a0}));
      }
      static std::shared_ptr<Expr::expr>
      Add_(const std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> &a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(Add{a0}));
      }
      static std::shared_ptr<Expr::expr>
      Mul_(const std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> &a0) {
        return std::shared_ptr<Expr::expr>(new Expr::expr(Mul{a0}));
      }
      static std::unique_ptr<Expr::expr> Lit_uptr(unsigned int a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(Lit{a0}));
      }
      static std::unique_ptr<Expr::expr> Add_uptr(
          const std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> &a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(Add{a0}));
      }
      static std::unique_ptr<Expr::expr> Mul_uptr(
          const std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> &a0) {
        return std::unique_ptr<Expr::expr>(new Expr::expr(Mul{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int eval() const {
      return std::visit(
          Overloaded{
              [](const typename Expr::expr::Lit _args) -> unsigned int {
                unsigned int n = _args._a0;
                return std::move(n);
              },
              [](const typename Expr::expr::Add _args) -> unsigned int {
                std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> es =
                    _args._a0;
                std::function<unsigned int(
                    std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>)>
                    sum_all;
                sum_all =
                    [&](std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>
                            l) -> unsigned int {
                  return std::visit(
                      Overloaded{[](const typename List::list<
                                     std::shared_ptr<Expr::expr>>::nil _args)
                                     -> unsigned int { return 0; },
                                 [&](const typename List::list<
                                     std::shared_ptr<Expr::expr>>::cons _args)
                                     -> unsigned int {
                                   std::shared_ptr<Expr::expr> e_ = _args._a0;
                                   std::shared_ptr<
                                       List::list<std::shared_ptr<Expr::expr>>>
                                       rest = _args._a1;
                                   return (std::move(e_)->eval() +
                                           sum_all(std::move(rest)));
                                 }},
                      l->v());
                };
                return sum_all(es);
              },
              [](const typename Expr::expr::Mul _args) -> unsigned int {
                std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> es =
                    _args._a0;
                std::function<unsigned int(
                    std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>)>
                    prod_all;
                prod_all =
                    [&](std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>
                            l) -> unsigned int {
                  return std::visit(
                      Overloaded{[](const typename List::list<
                                     std::shared_ptr<Expr::expr>>::nil _args)
                                     -> unsigned int { return (0 + 1); },
                                 [&](const typename List::list<
                                     std::shared_ptr<Expr::expr>>::cons _args)
                                     -> unsigned int {
                                   std::shared_ptr<Expr::expr> e_ = _args._a0;
                                   std::shared_ptr<
                                       List::list<std::shared_ptr<Expr::expr>>>
                                       rest = _args._a1;
                                   return (std::move(e_)->eval() *
                                           prod_all(std::move(rest)));
                                 }},
                      l->v());
                };
                return prod_all(es);
              }},
          this->v());
    }
    std::shared_ptr<List::list<unsigned int>> literals() const {
      return std::visit(
          Overloaded{
              [](const typename Expr::expr::Lit _args)
                  -> std::shared_ptr<List::list<unsigned int>> {
                unsigned int n = _args._a0;
                return List::list<unsigned int>::ctor::cons_(
                    std::move(n), List::list<unsigned int>::ctor::nil_());
              },
              [](const typename Expr::expr::Add _args)
                  -> std::shared_ptr<List::list<unsigned int>> {
                std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> es =
                    _args._a0;
                std::function<std::shared_ptr<List::list<unsigned int>>(
                    std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>)>
                    aux;
                aux =
                    [&](std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>
                            l) -> std::shared_ptr<List::list<unsigned int>> {
                  return std::visit(
                      Overloaded{
                          [](const typename List::list<
                              std::shared_ptr<Expr::expr>>::nil _args)
                              -> std::shared_ptr<List::list<unsigned int>> {
                            return List::list<unsigned int>::ctor::nil_();
                          },
                          [&](const typename List::list<
                              std::shared_ptr<Expr::expr>>::cons _args)
                              -> std::shared_ptr<List::list<unsigned int>> {
                            std::shared_ptr<Expr::expr> e_ = _args._a0;
                            std::shared_ptr<
                                List::list<std::shared_ptr<Expr::expr>>>
                                rest = _args._a1;
                            return std::move(e_)->literals()->app(
                                aux(std::move(rest)));
                          }},
                      l->v());
                };
                return aux(es);
              },
              [](const typename Expr::expr::Mul _args)
                  -> std::shared_ptr<List::list<unsigned int>> {
                std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>> es =
                    _args._a0;
                std::function<std::shared_ptr<List::list<unsigned int>>(
                    std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>)>
                    aux;
                aux =
                    [&](std::shared_ptr<List::list<std::shared_ptr<Expr::expr>>>
                            l) -> std::shared_ptr<List::list<unsigned int>> {
                  return std::visit(
                      Overloaded{
                          [](const typename List::list<
                              std::shared_ptr<Expr::expr>>::nil _args)
                              -> std::shared_ptr<List::list<unsigned int>> {
                            return List::list<unsigned int>::ctor::nil_();
                          },
                          [&](const typename List::list<
                              std::shared_ptr<Expr::expr>>::cons _args)
                              -> std::shared_ptr<List::list<unsigned int>> {
                            std::shared_ptr<Expr::expr> e_ = _args._a0;
                            std::shared_ptr<
                                List::list<std::shared_ptr<Expr::expr>>>
                                rest = _args._a1;
                            return std::move(e_)->literals()->app(
                                aux(std::move(rest)));
                          }},
                      l->v());
                };
                return aux(es);
              }},
          this->v());
    }
  };
};

const std::shared_ptr<Expr::expr> test_add =
    Expr::expr::ctor::Add_(List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
        Expr::expr::ctor::Lit_((0 + 1)),
        List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
            Expr::expr::ctor::Lit_(((0 + 1) + 1)),
            List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
                Expr::expr::ctor::Lit_((((0 + 1) + 1) + 1)),
                List::list<std::shared_ptr<Expr::expr>>::ctor::nil_()))));

const std::shared_ptr<Expr::expr> test_mul =
    Expr::expr::ctor::Mul_(List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
        Expr::expr::ctor::Lit_(((0 + 1) + 1)),
        List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
            Expr::expr::ctor::Lit_((((0 + 1) + 1) + 1)),
            List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
                Expr::expr::ctor::Lit_(((((0 + 1) + 1) + 1) + 1)),
                List::list<std::shared_ptr<Expr::expr>>::ctor::nil_()))));

const std::shared_ptr<Expr::expr> test_nested =
    Expr::expr::ctor::Mul_(List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
        Expr::expr::ctor::Add_(
            List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
                Expr::expr::ctor::Lit_((0 + 1)),
                List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
                    Expr::expr::ctor::Lit_(((0 + 1) + 1)),
                    List::list<std::shared_ptr<Expr::expr>>::ctor::nil_()))),
        List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
            Expr::expr::ctor::Add_(
                List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
                    Expr::expr::ctor::Lit_((((0 + 1) + 1) + 1)),
                    List::list<std::shared_ptr<Expr::expr>>::ctor::cons_(
                        Expr::expr::ctor::Lit_(((((0 + 1) + 1) + 1) + 1)),
                        List::list<
                            std::shared_ptr<Expr::expr>>::ctor::nil_()))),
            List::list<std::shared_ptr<Expr::expr>>::ctor::nil_())));

const unsigned int test_eval_add = test_add->eval();

const unsigned int test_eval_mul = test_mul->eval();

const unsigned int test_eval_nested = test_nested->eval();

const std::shared_ptr<List::list<unsigned int>> test_literals =
    test_nested->literals();
