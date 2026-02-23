#include "lazy.h"
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
  };
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::shared_ptr<List::list<T2>> map(F0 &&f,
                                    const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T2>> {
                                 return List::list<T2>::ctor::nil_();
                               },
                               [&](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T2>> {
                                 T1 a = _args._a0;
                                 std::shared_ptr<List::list<T1>> l0 = _args._a1;
                                 return List::list<T2>::ctor::cons_(
                                     f(a), map<T1, T2>(f, std::move(l0)));
                               }},
                    l->v());
}

struct Colist {
  template <typename A> struct colist {
  public:
    struct conil {};
    struct cocons {
      A _a0;
      std::shared_ptr<Colist::colist<A>> _a1;
    };
    using variant_t = std::variant<conil, cocons>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit colist(conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit colist(cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Colist::colist<A>> conil_() {
        return std::shared_ptr<Colist::colist<A>>(
            new Colist::colist<A>(conil{}));
      }
      static std::shared_ptr<Colist::colist<A>>
      cocons_(A a0, const std::shared_ptr<Colist::colist<A>> &a1) {
        return std::shared_ptr<Colist::colist<A>>(
            new Colist::colist<A>(cocons{a0, a1}));
      }
      static std::unique_ptr<Colist::colist<A>> conil_uptr() {
        return std::unique_ptr<Colist::colist<A>>(
            new Colist::colist<A>(conil{}));
      }
      static std::unique_ptr<Colist::colist<A>>
      cocons_uptr(A a0, const std::shared_ptr<Colist::colist<A>> &a1) {
        return std::unique_ptr<Colist::colist<A>>(
            new Colist::colist<A>(cocons{a0, a1}));
      }
      static std::shared_ptr<Colist::colist<A>>
      lazy_(std::function<std::shared_ptr<Colist::colist<A>>()> thunk) {
        return std::shared_ptr<Colist::colist<A>>(new Colist::colist<A>(
            std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<Colist::colist<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<Colist::colist<T2>> comap(F0 &&f) const {
      return Colist::colist<T2>::ctor::lazy_(
          [=](void) -> std::shared_ptr<Colist::colist<T2>> {
            return std::visit(
                Overloaded{[](const typename Colist::colist<A>::conil _args)
                               -> std::shared_ptr<Colist::colist<T2>> {
                             return Colist::colist<T2>::ctor::conil_();
                           },
                           [&](const typename Colist::colist<A>::cocons _args)
                               -> std::shared_ptr<Colist::colist<T2>> {
                             A x = _args._a0;
                             std::shared_ptr<Colist::colist<A>> xs = _args._a1;
                             return Colist::colist<T2>::ctor::cocons_(
                                 f(x), xs->comap(f));
                           }},
                this->v());
          });
    }
    std::shared_ptr<List::list<A>>
    list_of_colist(const unsigned int fuel) const {
      if (fuel <= 0) {
        return List::list<A>::ctor::nil_();
      } else {
        unsigned int fuel_ = fuel - 1;
        return std::visit(
            Overloaded{[](const typename Colist::colist<A>::conil _args)
                           -> std::shared_ptr<List::list<A>> {
                         return List::list<A>::ctor::nil_();
                       },
                       [&](const typename Colist::colist<A>::cocons _args)
                           -> std::shared_ptr<List::list<A>> {
                         A x = _args._a0;
                         std::shared_ptr<Colist::colist<A>> xs = _args._a1;
                         return List::list<A>::ctor::cons_(
                             x, xs->list_of_colist(fuel_));
                       }},
            this->v());
      }
    }
  };
};

struct Cotree {
  template <typename A> struct cotree {
  public:
    struct conode {
      A _a0;
      std::shared_ptr<Colist::colist<std::shared_ptr<Cotree::cotree<A>>>> _a1;
    };
    using variant_t = std::variant<conode>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit cotree(conode _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit cotree(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Cotree::cotree<A>>
      conode_(A a0,
              const std::shared_ptr<
                  Colist::colist<std::shared_ptr<Cotree::cotree<A>>>> &a1) {
        return std::shared_ptr<Cotree::cotree<A>>(
            new Cotree::cotree<A>(conode{a0, a1}));
      }
      static std::unique_ptr<Cotree::cotree<A>>
      conode_uptr(A a0,
                  const std::shared_ptr<
                      Colist::colist<std::shared_ptr<Cotree::cotree<A>>>> &a1) {
        return std::unique_ptr<Cotree::cotree<A>>(
            new Cotree::cotree<A>(conode{a0, a1}));
      }
      static std::shared_ptr<Cotree::cotree<A>>
      lazy_(std::function<std::shared_ptr<Cotree::cotree<A>>()> thunk) {
        return std::shared_ptr<Cotree::cotree<A>>(new Cotree::cotree<A>(
            std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<Cotree::cotree<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    A root() const {
      return std::visit(
          Overloaded{
              [](const typename Cotree::cotree<A>::conode _args) -> auto {
                A a = _args._a0;
                return a;
              }},
          this->v());
    }
    std::shared_ptr<Colist::colist<std::shared_ptr<Cotree::cotree<A>>>>
    children() const {
      return Colist::colist<std::shared_ptr<Cotree::cotree<A>>>::ctor::lazy_(
          [=](void) -> std::shared_ptr<
                        Colist::colist<std::shared_ptr<Cotree::cotree<A>>>> {
            return std::visit(
                Overloaded{[](const typename Cotree::cotree<A>::conode _args)
                               -> std::shared_ptr<Colist::colist<
                                   std::shared_ptr<Cotree::cotree<A>>>> {
                  std::shared_ptr<
                      Colist::colist<std::shared_ptr<Cotree::cotree<A>>>>
                      f = _args._a1;
                  return f;
                }},
                this->v());
          });
    }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<Cotree::cotree<T2>> comap_cotree(F0 &&g) const {
      return Cotree::cotree<T2>::ctor::lazy_(
          [=](void) -> std::shared_ptr<Cotree::cotree<T2>> {
            return std::visit(
                Overloaded{[&](const typename Cotree::cotree<A>::conode _args)
                               -> std::shared_ptr<Cotree::cotree<T2>> {
                  A a = _args._a0;
                  std::shared_ptr<
                      Colist::colist<std::shared_ptr<Cotree::cotree<A>>>>
                      f = _args._a1;
                  return Cotree::cotree<T2>::ctor::conode_(
                      g(a),
                      f->comap(
                          [&](const std::shared_ptr<Cotree::cotree<A>> _x0) {
                            return _x0->comap_cotree(g);
                          }));
                }},
                this->v());
          });
    }
  };
};

struct Tree {
  template <typename A> struct tree {
  public:
    struct node {
      A _a0;
      std::shared_ptr<List::list<std::shared_ptr<Tree::tree<A>>>> _a1;
    };
    using variant_t = std::variant<node>;

  private:
    variant_t v_;
    explicit tree(node _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Tree::tree<A>>
      node_(A a0,
            const std::shared_ptr<List::list<std::shared_ptr<Tree::tree<A>>>>
                &a1) {
        return std::shared_ptr<Tree::tree<A>>(new Tree::tree<A>(node{a0, a1}));
      }
      static std::unique_ptr<Tree::tree<A>> node_uptr(
          A a0,
          const std::shared_ptr<List::list<std::shared_ptr<Tree::tree<A>>>>
              &a1) {
        return std::unique_ptr<Tree::tree<A>>(new Tree::tree<A>(node{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    A tree_root() const {
      return std::visit(
          Overloaded{[](const typename Tree::tree<A>::node _args) -> auto {
            A a = _args._a0;
            return a;
          }},
          this->v());
    }
  };
};

template <typename T1>
std::shared_ptr<Cotree::cotree<T1>> singleton_cotree(const T1 a) {
  return Cotree::cotree<
      T1>::ctor::lazy_([=](void) -> std::shared_ptr<Cotree::cotree<T1>> {
    return Cotree::cotree<T1>::ctor::conode_(
        a, Colist::colist<std::shared_ptr<Cotree::cotree<T1>>>::ctor::conil_());
  });
}

template <typename T1, MapsTo<std::shared_ptr<Colist::colist<T1>>, T1> F0>
std::shared_ptr<Cotree::cotree<T1>> unfold_cotree(F0 &&next, const T1 init) {
  return Cotree::cotree<T1>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Cotree::cotree<T1>> {
        return Cotree::cotree<T1>::ctor::conode_(
            init, next(init)->comap([&](const T1 _x0) {
              return unfold_cotree<T1>(next, _x0);
            }));
      });
}

template <typename T1>
std::shared_ptr<Tree::tree<T1>>
tree_of_cotree(const unsigned int fuel,
               const std::shared_ptr<Cotree::cotree<T1>> &t) {
  return std::visit(
      Overloaded{[&](const typename Cotree::cotree<T1>::conode _args)
                     -> std::shared_ptr<Tree::tree<T1>> {
        T1 a = _args._a0;
        std::shared_ptr<Colist::colist<std::shared_ptr<Cotree::cotree<T1>>>> f =
            _args._a1;
        if (fuel <= 0) {
          return Tree::tree<T1>::ctor::node_(
              a, List::list<std::shared_ptr<Tree::tree<T1>>>::ctor::nil_());
        } else {
          unsigned int fuel_ = fuel - 1;
          return Tree::tree<T1>::ctor::node_(
              a, map<std::shared_ptr<Cotree::cotree<T1>>,
                     std::shared_ptr<Tree::tree<T1>>>(
                     [&](const std::shared_ptr<Cotree::cotree<T1>> _x0) {
                       return tree_of_cotree<T1>(fuel_, _x0);
                     },
                     f->list_of_colist(fuel)));
        }
      }},
      t->v());
}

const std::shared_ptr<Cotree::cotree<unsigned int>> sample_cotree =
    Cotree::cotree<unsigned int>::ctor::conode_(
        (0 + 1),
        Colist::colist<std::shared_ptr<Cotree::cotree<unsigned int>>>::ctor::
            cocons_(
                singleton_cotree<unsigned int>(((0 + 1) + 1)),
                Colist::colist<std::shared_ptr<Cotree::cotree<unsigned int>>>::
                    ctor::cocons_(
                        singleton_cotree<unsigned int>((((0 + 1) + 1) + 1)),
                        Colist::colist<std::shared_ptr<
                            Cotree::cotree<unsigned int>>>::ctor::conil_())));

const unsigned int test_root = sample_cotree->root();

const unsigned int test_doubled_root =
    sample_cotree
        ->comap_cotree([](unsigned int n) { return (n * ((0 + 1) + 1)); })
        ->root();

std::shared_ptr<Colist::colist<unsigned int>> nats(const unsigned int n);

const std::shared_ptr<List::list<unsigned int>> test_first_five =
    nats(0)->list_of_colist((((((0 + 1) + 1) + 1) + 1) + 1));

std::shared_ptr<Colist::colist<unsigned int>>
binary_children(const unsigned int n);

const std::shared_ptr<Cotree::cotree<unsigned int>> binary_tree =
    unfold_cotree<unsigned int>(binary_children, 0);

const unsigned int test_binary_root = binary_tree->root();

const std::shared_ptr<Tree::tree<unsigned int>> test_approx =
    tree_of_cotree<unsigned int>(((0 + 1) + 1), binary_tree);

const unsigned int test_approx_root = test_approx->tree_root();
