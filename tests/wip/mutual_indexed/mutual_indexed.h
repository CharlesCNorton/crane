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

struct EvenTree;
struct OddTree;
struct EvenTree {
  struct evenTree {
  public:
    struct ELeaf {};
    struct ENode {
      unsigned int _a0;
      unsigned int _a1;
      std::shared_ptr<OddTree::oddTree> _a2;
    };
    using variant_t = std::variant<ELeaf, ENode>;

  private:
    variant_t v_;
    explicit evenTree(ELeaf _v) : v_(std::move(_v)) {}
    explicit evenTree(ENode _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<EvenTree::evenTree> ELeaf_() {
        return std::shared_ptr<EvenTree::evenTree>(
            new EvenTree::evenTree(ELeaf{}));
      }
      static std::shared_ptr<EvenTree::evenTree>
      ENode_(unsigned int a0, unsigned int a1,
             const std::shared_ptr<OddTree::oddTree> &a2) {
        return std::shared_ptr<EvenTree::evenTree>(
            new EvenTree::evenTree(ENode{a0, a1, a2}));
      }
      static std::unique_ptr<EvenTree::evenTree> ELeaf_uptr() {
        return std::unique_ptr<EvenTree::evenTree>(
            new EvenTree::evenTree(ELeaf{}));
      }
      static std::unique_ptr<EvenTree::evenTree>
      ENode_uptr(unsigned int a0, unsigned int a1,
                 const std::shared_ptr<OddTree::oddTree> &a2) {
        return std::unique_ptr<EvenTree::evenTree>(
            new EvenTree::evenTree(ENode{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int even_val(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename EvenTree::evenTree::ELeaf _args)
                         -> unsigned int { return 0; },
                     [](const typename EvenTree::evenTree::ENode _args)
                         -> unsigned int {
                       unsigned int v = _args._a1;
                       return std::move(v);
                     }},
          this->v());
    }
  };
};
struct OddTree {
  struct oddTree {
  public:
    struct ONode {
      unsigned int _a0;
      unsigned int _a1;
      std::shared_ptr<EvenTree::evenTree> _a2;
    };
    using variant_t = std::variant<ONode>;

  private:
    variant_t v_;
    explicit oddTree(ONode _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<OddTree::oddTree>
      ONode_(unsigned int a0, unsigned int a1,
             const std::shared_ptr<EvenTree::evenTree> &a2) {
        return std::shared_ptr<OddTree::oddTree>(
            new OddTree::oddTree(ONode{a0, a1, a2}));
      }
      static std::unique_ptr<OddTree::oddTree>
      ONode_uptr(unsigned int a0, unsigned int a1,
                 const std::shared_ptr<EvenTree::evenTree> &a2) {
        return std::unique_ptr<OddTree::oddTree>(
            new OddTree::oddTree(ONode{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int odd_val(const unsigned int _x) const {
      return std::visit(
          Overloaded{
              [](const typename OddTree::oddTree::ONode _args) -> unsigned int {
                unsigned int v = _args._a1;
                return std::move(v);
              }},
          this->v());
    }
  };
};

const std::shared_ptr<EvenTree::evenTree> leaf =
    EvenTree::evenTree::ctor::ELeaf_();

const std::shared_ptr<OddTree::oddTree> tree1 = OddTree::oddTree::ctor::ONode_(
    0, ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
    EvenTree::evenTree::ctor::ELeaf_());

const std::shared_ptr<EvenTree::evenTree> tree2 =
    EvenTree::evenTree::ctor::ENode_(
        (0 + 1),
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
        OddTree::oddTree::ctor::ONode_(
            0, ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
            EvenTree::evenTree::ctor::ELeaf_()));

const unsigned int test_leaf_val = leaf->even_val(0);

const unsigned int test_tree1_val = tree1->odd_val((0 + 1));

const unsigned int test_tree2_val = tree2->even_val(((0 + 1) + 1));
