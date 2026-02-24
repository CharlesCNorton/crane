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

struct Ppair {
  template <typename A, typename B> struct ppair {
  public:
    struct PPair {
      A _a0;
      B _a1;
    };
    using variant_t = std::variant<PPair>;

  private:
    variant_t v_;
    explicit ppair(PPair _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Ppair::ppair<A, B>> PPair_(A a0, B a1) {
        return std::shared_ptr<Ppair::ppair<A, B>>(
            new Ppair::ppair<A, B>(PPair{a0, a1}));
      }
      static std::unique_ptr<Ppair::ppair<A, B>> PPair_uptr(A a0, B a1) {
        return std::unique_ptr<Ppair::ppair<A, B>>(
            new Ppair::ppair<A, B>(PPair{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    A pfst() const {
      return std::visit(
          Overloaded{
              [](const typename Ppair::ppair<A, B>::PPair _args) -> auto {
                A a = _args._a0;
                return a;
              }},
          this->v());
    }
    B psnd() const {
      return std::visit(
          Overloaded{
              [](const typename Ppair::ppair<A, B>::PPair _args) -> auto {
                B b = _args._a1;
                return b;
              }},
          this->v());
    }
  };
};

struct Pmaybe {
  template <typename A> struct pmaybe {
  public:
    struct PNothing {};
    struct PJust {
      A _a0;
    };
    using variant_t = std::variant<PNothing, PJust>;

  private:
    variant_t v_;
    explicit pmaybe(PNothing _v) : v_(std::move(_v)) {}
    explicit pmaybe(PJust _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Pmaybe::pmaybe<A>> PNothing_() {
        return std::shared_ptr<Pmaybe::pmaybe<A>>(
            new Pmaybe::pmaybe<A>(PNothing{}));
      }
      static std::shared_ptr<Pmaybe::pmaybe<A>> PJust_(A a0) {
        return std::shared_ptr<Pmaybe::pmaybe<A>>(
            new Pmaybe::pmaybe<A>(PJust{a0}));
      }
      static std::unique_ptr<Pmaybe::pmaybe<A>> PNothing_uptr() {
        return std::unique_ptr<Pmaybe::pmaybe<A>>(
            new Pmaybe::pmaybe<A>(PNothing{}));
      }
      static std::unique_ptr<Pmaybe::pmaybe<A>> PJust_uptr(A a0) {
        return std::unique_ptr<Pmaybe::pmaybe<A>>(
            new Pmaybe::pmaybe<A>(PJust{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    A pmaybe_default(const A d) const {
      return std::visit(
          Overloaded{[&](const typename Pmaybe::pmaybe<A>::PNothing _args)
                         -> auto { return d; },
                     [](const typename Pmaybe::pmaybe<A>::PJust _args) -> auto {
                       A x = _args._a0;
                       return x;
                     }},
          this->v());
    }
  };
};

struct Ptree {
  template <typename A> struct ptree {
  public:
    struct PLeaf {
      A _a0;
    };
    struct PNode {
      std::shared_ptr<Ptree::ptree<A>> _a0;
      std::shared_ptr<Ptree::ptree<A>> _a1;
    };
    using variant_t = std::variant<PLeaf, PNode>;

  private:
    variant_t v_;
    explicit ptree(PLeaf _v) : v_(std::move(_v)) {}
    explicit ptree(PNode _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Ptree::ptree<A>> PLeaf_(A a0) {
        return std::shared_ptr<Ptree::ptree<A>>(new Ptree::ptree<A>(PLeaf{a0}));
      }
      static std::shared_ptr<Ptree::ptree<A>>
      PNode_(const std::shared_ptr<Ptree::ptree<A>> &a0,
             const std::shared_ptr<Ptree::ptree<A>> &a1) {
        return std::shared_ptr<Ptree::ptree<A>>(
            new Ptree::ptree<A>(PNode{a0, a1}));
      }
      static std::unique_ptr<Ptree::ptree<A>> PLeaf_uptr(A a0) {
        return std::unique_ptr<Ptree::ptree<A>>(new Ptree::ptree<A>(PLeaf{a0}));
      }
      static std::unique_ptr<Ptree::ptree<A>>
      PNode_uptr(const std::shared_ptr<Ptree::ptree<A>> &a0,
                 const std::shared_ptr<Ptree::ptree<A>> &a1) {
        return std::unique_ptr<Ptree::ptree<A>>(
            new Ptree::ptree<A>(PNode{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int ptree_size() const {
      return std::visit(
          Overloaded{
              [](const typename Ptree::ptree<A>::PLeaf _args) -> unsigned int {
                return (0 + 1);
              },
              [](const typename Ptree::ptree<A>::PNode _args) -> unsigned int {
                std::shared_ptr<Ptree::ptree<A>> l = _args._a0;
                std::shared_ptr<Ptree::ptree<A>> r = _args._a1;
                return (
                    (std::move(l)->ptree_size() + std::move(r)->ptree_size()) +
                    1);
              }},
          this->v());
    }
  };
};

const unsigned int test_ppair_fst =
    Ppair::ppair<unsigned int, bool>::ctor::PPair_(
        (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1), true)
        ->pfst();

const bool test_ppair_snd =
    Ppair::ppair<unsigned int, bool>::ctor::PPair_(
        (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1), true)
        ->psnd();

const unsigned int test_pjust = Pmaybe::pmaybe<unsigned int>::ctor::PJust_((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))->pmaybe_default(0);

const unsigned int test_pnothing =
    Pmaybe::pmaybe<unsigned int>::ctor::PNothing_()->pmaybe_default(0);

const unsigned int test_ptree =
    Ptree::ptree<unsigned int>::ctor::PNode_(
        Ptree::ptree<unsigned int>::ctor::PLeaf_((0 + 1)),
        Ptree::ptree<unsigned int>::ctor::PNode_(
            Ptree::ptree<unsigned int>::ctor::PLeaf_(((0 + 1) + 1)),
            Ptree::ptree<unsigned int>::ctor::PLeaf_((((0 + 1) + 1) + 1))))
        ->ptree_size();
