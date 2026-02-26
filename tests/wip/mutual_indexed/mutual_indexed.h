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

struct MutualIndexed {
  struct EvenTree;
  struct OddTree;
  struct evenTree {
  public:
    struct ELeaf {};
    struct ENode {
      unsigned int _a0;
      unsigned int _a1;
      std::shared_ptr<oddTree> _a2;
    };
    using variant_t = std::variant<ELeaf, ENode>;

  private:
    variant_t v_;
    explicit evenTree(ELeaf _v) : v_(std::move(_v)) {}
    explicit evenTree(ENode _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<evenTree> ELeaf_() {
        return std::shared_ptr<evenTree>(new evenTree(ELeaf{}));
      }
      static std::shared_ptr<evenTree>
      ENode_(unsigned int a0, unsigned int a1,
             const std::shared_ptr<oddTree> &a2) {
        return std::shared_ptr<evenTree>(new evenTree(ENode{a0, a1, a2}));
      }
      static std::unique_ptr<evenTree> ELeaf_uptr() {
        return std::unique_ptr<evenTree>(new evenTree(ELeaf{}));
      }
      static std::unique_ptr<evenTree>
      ENode_uptr(unsigned int a0, unsigned int a1,
                 const std::shared_ptr<oddTree> &a2) {
        return std::unique_ptr<evenTree>(new evenTree(ENode{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
  struct oddTree {
  public:
    struct ONode {
      unsigned int _a0;
      unsigned int _a1;
      std::shared_ptr<evenTree> _a2;
    };
    using variant_t = std::variant<ONode>;

  private:
    variant_t v_;
    explicit oddTree(ONode _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<oddTree>
      ONode_(unsigned int a0, unsigned int a1,
             const std::shared_ptr<evenTree> &a2) {
        return std::shared_ptr<oddTree>(new oddTree(ONode{a0, a1, a2}));
      }
      static std::unique_ptr<oddTree>
      ONode_uptr(unsigned int a0, unsigned int a1,
                 const std::shared_ptr<evenTree> &a2) {
        return std::unique_ptr<oddTree>(new oddTree(ONode{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<oddTree>> F1>
  static T1 EvenTree_rect(const T1 f, F1 &&f0, const unsigned int _x,
                          const std::shared_ptr<evenTree> &e) {
    return std::visit(
        Overloaded{
            [&](const typename evenTree::ELeaf _args) -> T1 { return f; },
            [&](const typename evenTree::ENode _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              std::shared_ptr<oddTree> o = _args._a2;
              return f0(std::move(n), std::move(n0), std::move(o));
            }},
        e->v());
  }

  template <typename T1,
            MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<oddTree>> F1>
  static T1 EvenTree_rec(const T1 f, F1 &&f0, const unsigned int _x,
                         const std::shared_ptr<evenTree> &e) {
    return std::visit(
        Overloaded{
            [&](const typename evenTree::ELeaf _args) -> T1 { return f; },
            [&](const typename evenTree::ENode _args) -> T1 {
              unsigned int n = _args._a0;
              unsigned int n0 = _args._a1;
              std::shared_ptr<oddTree> o = _args._a2;
              return f0(std::move(n), std::move(n0), std::move(o));
            }},
        e->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<evenTree>> F0>
  static T1 OddTree_rect(F0 &&f, const unsigned int _x,
                         const std::shared_ptr<oddTree> &o) {
    return std::visit(
        Overloaded{[&](const typename oddTree::ONode _args) -> T1 {
          unsigned int n = _args._a0;
          unsigned int n0 = _args._a1;
          std::shared_ptr<evenTree> e = _args._a2;
          return f(std::move(n), std::move(n0), std::move(e));
        }},
        o->v());
  }

  template <
      typename T1,
      MapsTo<T1, unsigned int, unsigned int, std::shared_ptr<evenTree>> F0>
  static T1 OddTree_rec(F0 &&f, const unsigned int _x,
                        const std::shared_ptr<oddTree> &o) {
    return std::visit(
        Overloaded{[&](const typename oddTree::ONode _args) -> T1 {
          unsigned int n = _args._a0;
          unsigned int n0 = _args._a1;
          std::shared_ptr<evenTree> e = _args._a2;
          return f(std::move(n), std::move(n0), std::move(e));
        }},
        o->v());
  }

  static unsigned int even_val(const unsigned int _x,
                               const std::shared_ptr<evenTree> &t);

  static unsigned int odd_val(const unsigned int _x,
                              const std::shared_ptr<oddTree> &t);

  static inline const std::shared_ptr<evenTree> leaf = evenTree::ctor::ELeaf_();

  static inline const std::shared_ptr<oddTree> tree1 = oddTree::ctor::ONode_(
      0, ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
      evenTree::ctor::ELeaf_());

  static inline const std::shared_ptr<evenTree> tree2 = evenTree::ctor::ENode_(
      (0 + 1),
      ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
      oddTree::ctor::ONode_(
          0, ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
          evenTree::ctor::ELeaf_()));

  static inline const unsigned int test_leaf_val = even_val(0, leaf);

  static inline const unsigned int test_tree1_val = odd_val((0 + 1), tree1);

  static inline const unsigned int test_tree2_val =
      even_val(((0 + 1) + 1), tree2);
};
