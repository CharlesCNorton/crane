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

bool even(const unsigned int n);

template <MapsTo<unsigned int, unsigned int> F1>
unsigned int fact_cps(const unsigned int n, F1 &&k) {
  if (n <= 0) {
    return k((0 + 1));
  } else {
    unsigned int n_ = n - 1;
    return fact_cps(n_, [&](unsigned int r) { return k(((n_ + 1) * r)); });
  }
}

unsigned int factorial(const unsigned int n);

template <MapsTo<unsigned int, unsigned int> F1>
unsigned int fib_cps(const unsigned int n, F1 &&k) {
  if (n <= 0) {
    return k(0);
  } else {
    unsigned int n1 = n - 1;
    if (n1 <= 0) {
      return k((0 + 1));
    } else {
      unsigned int n_ = n1 - 1;
      return fib_cps(n_, [&](unsigned int a) {
        return fib_cps(n1, [&](unsigned int b) { return k((a + b)); });
      });
    }
  }
}

unsigned int fibonacci(const unsigned int n);

struct Tree {
  struct tree {
  public:
    struct Leaf {
      unsigned int _a0;
    };
    struct Node {
      std::shared_ptr<Tree::tree> _a0;
      std::shared_ptr<Tree::tree> _a1;
    };
    using variant_t = std::variant<Leaf, Node>;

  private:
    variant_t v_;
    explicit tree(Leaf _v) : v_(std::move(_v)) {}
    explicit tree(Node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Tree::tree> Leaf_(unsigned int a0) {
        return std::shared_ptr<Tree::tree>(new Tree::tree(Leaf{a0}));
      }
      static std::shared_ptr<Tree::tree>
      Node_(const std::shared_ptr<Tree::tree> &a0,
            const std::shared_ptr<Tree::tree> &a1) {
        return std::shared_ptr<Tree::tree>(new Tree::tree(Node{a0, a1}));
      }
      static std::unique_ptr<Tree::tree> Leaf_uptr(unsigned int a0) {
        return std::unique_ptr<Tree::tree>(new Tree::tree(Leaf{a0}));
      }
      static std::unique_ptr<Tree::tree>
      Node_uptr(const std::shared_ptr<Tree::tree> &a0,
                const std::shared_ptr<Tree::tree> &a1) {
        return std::unique_ptr<Tree::tree>(new Tree::tree(Node{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    template <MapsTo<unsigned int, unsigned int> F0>
    unsigned int tree_sum_cps(F0 &&k) const {
      return std::visit(
          Overloaded{
              [&](const typename Tree::tree::Leaf _args) -> unsigned int {
                unsigned int n = _args._a0;
                return k(std::move(n));
              },
              [&](const typename Tree::tree::Node _args) -> unsigned int {
                std::shared_ptr<Tree::tree> l = _args._a0;
                std::shared_ptr<Tree::tree> r = _args._a1;
                return std::move(l)->tree_sum_cps([&](unsigned int sl) {
                  return r->tree_sum_cps(
                      [&](unsigned int sr) { return k((sl + sr)); });
                });
              }},
          this->v());
    }
    unsigned int tree_sum() const {
      return this->tree_sum_cps([](unsigned int x) { return x; });
    }
  };
};

template <MapsTo<unsigned int, unsigned int> F1>
unsigned int sum_cps(const std::shared_ptr<List::list<unsigned int>> &l,
                     F1 &&k) {
  return std::visit(
      Overloaded{[&](const typename List::list<unsigned int>::nil _args)
                     -> unsigned int { return k(0); },
                 [&](const typename List::list<unsigned int>::cons _args)
                     -> unsigned int {
                   unsigned int x = _args._a0;
                   std::shared_ptr<List::list<unsigned int>> rest = _args._a1;
                   return sum_cps(std::move(rest),
                                  [&](unsigned int r) { return k((x + r)); });
                 }},
      l->v());
}

unsigned int list_sum(const std::shared_ptr<List::list<unsigned int>> &l);

template <MapsTo<bool, unsigned int> F0,
          MapsTo<unsigned int, std::shared_ptr<List::list<unsigned int>>,
                 std::shared_ptr<List::list<unsigned int>>>
              F2>
unsigned int partition_cps(F0 &&p,
                           const std::shared_ptr<List::list<unsigned int>> &l,
                           F2 &&k) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<unsigned int>::nil _args)
              -> unsigned int {
            return k(List::list<unsigned int>::ctor::nil_(),
                     List::list<unsigned int>::ctor::nil_());
          },
          [&](const typename List::list<unsigned int>::cons _args)
              -> unsigned int {
            unsigned int x = _args._a0;
            std::shared_ptr<List::list<unsigned int>> rest = _args._a1;
            return partition_cps(
                p, std::move(rest),
                [&](std::shared_ptr<List::list<unsigned int>> yes,
                    std::shared_ptr<List::list<unsigned int>> no) {
                  if (p(x)) {
                    return k(List::list<unsigned int>::ctor::cons_(x, yes), no);
                  } else {
                    return k(yes, List::list<unsigned int>::ctor::cons_(x, no));
                  }
                });
          }},
      l->v());
}

unsigned int count_evens(const std::shared_ptr<List::list<unsigned int>> &l);

const unsigned int test_fact_5 = factorial((((((0 + 1) + 1) + 1) + 1) + 1));

const unsigned int test_fib_7 =
    fibonacci((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const unsigned int test_tree =
    Tree::tree::ctor::Node_(
        Tree::tree::ctor::Node_(Tree::tree::ctor::Leaf_((0 + 1)),
                                Tree::tree::ctor::Leaf_(((0 + 1) + 1))),
        Tree::tree::ctor::Leaf_((((0 + 1) + 1) + 1)))
        ->tree_sum();

const unsigned int test_list_sum =
    list_sum(List::list<unsigned int>::ctor::cons_(
        ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
        List::list<unsigned int>::ctor::cons_(
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
             1),
            List::list<unsigned int>::ctor::cons_(
                ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
                 1),
                List::list<unsigned int>::ctor::nil_()))));

const unsigned int test_evens =
    count_evens(List::list<unsigned int>::ctor::cons_(
        (0 + 1),
        List::list<unsigned int>::ctor::cons_(
            ((0 + 1) + 1),
            List::list<unsigned int>::ctor::cons_(
                (((0 + 1) + 1) + 1),
                List::list<unsigned int>::ctor::cons_(
                    ((((0 + 1) + 1) + 1) + 1),
                    List::list<unsigned int>::ctor::cons_(
                        (((((0 + 1) + 1) + 1) + 1) + 1),
                        List::list<unsigned int>::ctor::cons_(
                            ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                            List::list<unsigned int>::ctor::nil_())))))));
