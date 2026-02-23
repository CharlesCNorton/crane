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

template <typename T1, typename T2, typename T3,
          MapsTo<T1, std::function<std::any(std::any)>, T1> F0,
          MapsTo<T3, T2> F1>
T1 hk_map(F0 &&map_f, F1 &&f, const T1 x) {
  return map_f("dummy", "dummy", f, x);
}

struct Tree {
  template <typename A> struct tree {
  public:
    struct Leaf {
      A _a0;
    };
    struct Branch {
      std::shared_ptr<Tree::tree<A>> _a0;
      std::shared_ptr<Tree::tree<A>> _a1;
    };
    using variant_t = std::variant<Leaf, Branch>;

  private:
    variant_t v_;
    explicit tree(Leaf _v) : v_(std::move(_v)) {}
    explicit tree(Branch _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Tree::tree<A>> Leaf_(A a0) {
        return std::shared_ptr<Tree::tree<A>>(new Tree::tree<A>(Leaf{a0}));
      }
      static std::shared_ptr<Tree::tree<A>>
      Branch_(const std::shared_ptr<Tree::tree<A>> &a0,
              const std::shared_ptr<Tree::tree<A>> &a1) {
        return std::shared_ptr<Tree::tree<A>>(
            new Tree::tree<A>(Branch{a0, a1}));
      }
      static std::unique_ptr<Tree::tree<A>> Leaf_uptr(A a0) {
        return std::unique_ptr<Tree::tree<A>>(new Tree::tree<A>(Leaf{a0}));
      }
      static std::unique_ptr<Tree::tree<A>>
      Branch_uptr(const std::shared_ptr<Tree::tree<A>> &a0,
                  const std::shared_ptr<Tree::tree<A>> &a1) {
        return std::unique_ptr<Tree::tree<A>>(
            new Tree::tree<A>(Branch{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<Tree::tree<T2>> tree_map(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename Tree::tree<A>::Leaf _args)
                         -> std::shared_ptr<Tree::tree<T2>> {
                       A x = _args._a0;
                       return Tree::tree<T2>::ctor::Leaf_(f(x));
                     },
                     [&](const typename Tree::tree<A>::Branch _args)
                         -> std::shared_ptr<Tree::tree<T2>> {
                       std::shared_ptr<Tree::tree<A>> l = _args._a0;
                       std::shared_ptr<Tree::tree<A>> r = _args._a1;
                       return Tree::tree<T2>::ctor::Branch_(
                           std::move(l)->tree_map(f),
                           std::move(r)->tree_map(f));
                     }},
          this->v());
    }
    template <typename T2, MapsTo<T2, A> F0, MapsTo<T2, T2, T2> F1>
    T2 tree_fold(F0 &&leaf_f, F1 &&branch_f) const {
      return std::visit(
          Overloaded{[&](const typename Tree::tree<A>::Leaf _args) -> auto {
                       A x = _args._a0;
                       return leaf_f(x);
                     },
                     [&](const typename Tree::tree<A>::Branch _args) -> auto {
                       std::shared_ptr<Tree::tree<A>> l = _args._a0;
                       std::shared_ptr<Tree::tree<A>> r = _args._a1;
                       return branch_f(
                           std::move(l)->tree_fold(leaf_f, branch_f),
                           std::move(r)->tree_fold(leaf_f, branch_f));
                     }},
          this->v());
    }
    unsigned int tree_sum() const {
      return this->tree_fold(
          [](unsigned int x) { return x; },
          [](const unsigned int _x0, const unsigned int _x1) {
            return (_x0 + _x1);
          });
    }
    unsigned int tree_size() const {
      return this->tree_fold(
          [](A _x) { return (0 + 1); },
          [](const unsigned int _x0, const unsigned int _x1) {
            return (_x0 + _x1);
          });
    }
  };
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::optional<T2> map_option(F0 &&f, const std::optional<T1> o) {
  if (o.has_value()) {
    T1 x = *o;
    return std::make_optional<T2>(f(x));
  } else {
    return std::nullopt;
  }
}

const std::shared_ptr<Tree::tree<unsigned int>> test_tree =
    Tree::tree<unsigned int>::ctor::Branch_(
        Tree::tree<unsigned int>::ctor::Leaf_((0 + 1)),
        Tree::tree<unsigned int>::ctor::Branch_(
            Tree::tree<unsigned int>::ctor::Leaf_(((0 + 1) + 1)),
            Tree::tree<unsigned int>::ctor::Leaf_((((0 + 1) + 1) + 1))));

const unsigned int test_tree_sum = test_tree->tree_sum();

const unsigned int test_tree_size = test_tree->tree_size();

const std::shared_ptr<Tree::tree<unsigned int>> test_tree_map =
    test_tree->tree_map([](unsigned int n) { return (n * ((0 + 1) + 1)); });

const std::optional<unsigned int> test_hk_option =
    hk_map<unsigned int, unsigned int>(
        [](void) { return map_option; }(),
        [](unsigned int n) { return (n + (0 + 1)); },
        std::make_optional<unsigned int>((((((0 + 1) + 1) + 1) + 1) + 1)));

const std::shared_ptr<Tree::tree<unsigned int>> test_hk_tree =
    hk_map<unsigned int, unsigned int>(
        [](void) { return this->tree_map(); }(),
        [](unsigned int n) {
          return (n + ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                       1));
        },
        test_tree);
