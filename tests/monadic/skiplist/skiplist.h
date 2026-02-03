#include <algorithm>
#include <any>
#include <cstdlib>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <skipnode.h>
#include <string>
#include <utility>
#include <variant>
#include <vector>

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
    };
    const variant_t &v() const { return v_; }
    unsigned int length() const {
      return std::visit(
          Overloaded{
              [](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (l_->length() + 1);
              }},
          this->v());
    }
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

struct Nat {
  static bool eqb(const unsigned int n, const unsigned int m);

  static bool leb(const unsigned int n, const unsigned int m);

  static bool ltb(const unsigned int n, const unsigned int m);
};

template <typename T1>
std::shared_ptr<List::list<T1>> repeat(const T1 x, const unsigned int n) {
  if (n <= 0) {
    return List::list<T1>::ctor::nil_();
  } else {
    unsigned int k = n - 1;
    return List::list<T1>::ctor::cons_(x, repeat<T1>(x, k));
  }
}

template <typename T1>
std::shared_ptr<List::list<T1>>
firstn(const unsigned int n, const std::shared_ptr<List::list<T1>> &l) {
  if (n <= 0) {
    return List::list<T1>::ctor::nil_();
  } else {
    unsigned int n0 = n - 1;
    return std::visit(
        Overloaded{[](const typename List::list<T1>::nil _args)
                       -> std::shared_ptr<List::list<T1>> {
                     return List::list<T1>::ctor::nil_();
                   },
                   [&](const typename List::list<T1>::cons _args)
                       -> std::shared_ptr<List::list<T1>> {
                     T1 a = _args._a0;
                     std::shared_ptr<List::list<T1>> l0 = _args._a1;
                     return List::list<T1>::ctor::cons_(a, firstn<T1>(n0, l0));
                   }},
        l->v());
  }
}

template <typename T1>
std::shared_ptr<List::list<T1>> rev(const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 return List::list<T1>::ctor::nil_();
                               },
                               [](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 T1 x = _args._a0;
                                 std::shared_ptr<List::list<T1>> l_ = _args._a1;
                                 return rev<T1>(l_)->app(
                                     List::list<T1>::ctor::cons_(
                                         x, List::list<T1>::ctor::nil_()));
                               }},
                    l->v());
}

struct STM {};

struct TVar {};

struct SkipList {
  static inline const unsigned int maxLevels =
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1);

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred_go(F0 &&ltK, const unsigned int fuel,
              const std::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
              const unsigned int level) {
    if (fuel <= 0) {
      return curr;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              curr->forward[level]);
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> next = *nextOpt;
        if (ltK(next->key, target)) {
          return findPred_go<T1, T2>(ltK, fuel_, next, target, level);
        } else {
          return curr;
        }
      } else {
        return curr;
      }
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<SkipNode<T1, T2>>
  findPred(F0 &&ltK, const std::shared_ptr<SkipNode<T1, T2>> curr,
           const T1 target, const unsigned int level) {
    return findPred_go<T1, T2>(ltK, 10000u, curr, target, level);
  }

  template <typename K, typename V> struct TSkipList {
    std::shared_ptr<SkipNode<K, V>> slHead;
    unsigned int slMaxLevel;
    std::shared_ptr<stm::TVar<unsigned int>> slLevel;
  };

  template <typename T1, typename T2>
  static std::shared_ptr<SkipNode<T1, T2>>
  slHead(const std::shared_ptr<TSkipList<T1, T2>> &t) {
    return t->slHead;
  }

  template <typename T1, typename T2>
  static std::shared_ptr<stm::TVar<unsigned int>>
  slLevel(const std::shared_ptr<TSkipList<T1, T2>> &t) {
    return t->slLevel;
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
  findPath_aux(
      F0 &&ltK, const std::shared_ptr<SkipNode<T1, T2>> curr, const T1 target,
      const unsigned int level,
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &acc) {
    std::shared_ptr<SkipNode<T1, T2>> pred =
        findPred<T1, T2>(ltK, curr, target, level);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> acc_ =
        List::list<std::shared_ptr<SkipNode<T1, T2>>>::ctor::cons_(pred, acc);
    if (level <= 0) {
      return acc_;
    } else {
      unsigned int level_ = level - 1;
      return findPath_aux<T1, T2>(ltK, pred, target, level_, acc_);
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
  findPath(F0 &&ltK, const std::shared_ptr<TSkipList<T1, T2>> &sl,
           const T1 target) {
    unsigned int lvl = stm::readTVar<unsigned int>(sl->slLevel);
    return findPath_aux<T1, T2>(
        ltK, sl->slHead, target, lvl,
        List::list<std::shared_ptr<SkipNode<T1, T2>>>::ctor::nil_());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static std::optional<T2>
  lookup(F0 &&ltK, F1 &&eqK, const T1 k,
         const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> std::optional<T2> { return std::nullopt; },
            [&](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::
                    cons _args) -> std::optional<T2> {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  T2 v = stm::readTVar<T2>(node->value);
                  return std::make_optional<T2>(v);
                } else {
                  return std::nullopt;
                }
              } else {
                return std::nullopt;
              }
            }},
        path->v());
  }

  template <typename T1, typename T2>
  static void linkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                          const std::shared_ptr<SkipNode<T1, T2>> newNode,
                          const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> oldNext =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            pred->forward[level]);
    stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        pred->forward[level],
        std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(newNode));
    return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        newNode->forward[level], oldNext);
  }

  template <typename T1, typename T2>
  static void linkNode_aux(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &preds,
      const std::shared_ptr<SkipNode<T1, T2>> newNode,
      const unsigned int level) {
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> void {
              std::shared_ptr<SkipNode<T1, T2>> pred = _args._a0;
              std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
                  rest = _args._a1;
              if (level <= 0) {
                return linkAtLevel<T1, T2>(pred, newNode, 0);
              } else {
                unsigned int level_ = level - 1;
                linkAtLevel<T1, T2>(pred, newNode, level);
                return linkNode_aux<T1, T2>(rest, newNode, level_);
              }
            }},
        preds->v());
  }

  template <typename T1, typename T2>
  static std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
  extendPath(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &path,
      const std::shared_ptr<SkipNode<T1, T2>> head, const unsigned int needed) {
    unsigned int have = path->length();
    if (Nat::leb(needed, have)) {
      return path;
    } else {
      return path->app(repeat<std::shared_ptr<SkipNode<T1, T2>>>(
          head, (((needed - have) > needed ? 0 : (needed - have)))));
    }
  }

  template <typename T1, typename T2>
  static void
  linkNode(const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
               &path,
           const std::shared_ptr<SkipNode<T1, T2>> newNode) {
    unsigned int lvl = newNode->level;
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
        relevantPath =
            firstn<std::shared_ptr<SkipNode<T1, T2>>>((lvl + 1), path);
    return linkNode_aux<T1, T2>(
        rev<std::shared_ptr<SkipNode<T1, T2>>>(relevantPath), newNode, lvl);
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static void insert(F0 &&ltK, F1 &&eqK, const T1 k, const T2 v,
                     const std::shared_ptr<TSkipList<T1, T2>> &sl,
                     const unsigned int newLevel) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> fullPath =
        extendPath<T1, T2>(path, sl->slHead, (newLevel + 1));
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> void {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
                if (eqK(existing->key, k)) {
                  return stm::writeTVar<T2>(existing->value, v);
                } else {
                  std::shared_ptr<SkipNode<T1, T2>> newNode =
                      SkipNode<T1, T2>::create(k, v, newLevel);
                  linkNode<T1, T2>(fullPath, newNode);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(sl->slLevel);
                  if (Nat::ltb(curLvl, newLevel)) {
                    return stm::writeTVar<unsigned int>(sl->slLevel, newLevel);
                  } else {
                    return;
                  }
                }
              } else {
                std::shared_ptr<SkipNode<T1, T2>> newNode =
                    SkipNode<T1, T2>::create(k, v, newLevel);
                linkNode<T1, T2>(fullPath, newNode);
                unsigned int curLvl = stm::readTVar<unsigned int>(sl->slLevel);
                if (Nat::ltb(curLvl, newLevel)) {
                  return stm::writeTVar<unsigned int>(sl->slLevel, newLevel);
                } else {
                  return;
                }
              }
            }},
        fullPath->v());
  }

  template <typename T1, typename T2>
  static void unlinkAtLevel(const std::shared_ptr<SkipNode<T1, T2>> pred,
                            const std::shared_ptr<SkipNode<T1, T2>> target,
                            const unsigned int level) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> targetNext =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            target->forward[level]);
    return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        pred->forward[level], targetNext);
  }

  template <typename T1, typename T2>
  static void unlinkNode_aux(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &preds,
      const std::shared_ptr<SkipNode<T1, T2>> target,
      const unsigned int level) {
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> void {
              std::shared_ptr<SkipNode<T1, T2>> pred = _args._a0;
              std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
                  rest = _args._a1;
              if (level <= 0) {
                return unlinkAtLevel<T1, T2>(pred, target, 0);
              } else {
                unsigned int level_ = level - 1;
                unlinkAtLevel<T1, T2>(pred, target, level);
                return unlinkNode_aux<T1, T2>(rest, target, level_);
              }
            }},
        preds->v());
  }

  template <typename T1, typename T2>
  static void unlinkNode(
      const std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
          &path,
      const std::shared_ptr<SkipNode<T1, T2>> target) {
    unsigned int lvl = target->level;
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
        relevantPath =
            firstn<std::shared_ptr<SkipNode<T1, T2>>>((lvl + 1), path);
    return unlinkNode_aux<T1, T2>(
        rev<std::shared_ptr<SkipNode<T1, T2>>>(relevantPath), target, lvl);
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static void remove(F0 &&ltK, F1 &&eqK, const T1 k,
                     const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> void { return; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> void {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>>
                      fullPath = extendPath<T1, T2>(path, sl->slHead,
                                                    (node->level + 1));
                  return unlinkNode<T1, T2>(fullPath, node);
                } else {
                  return;
                }
              } else {
                return;
              }
            }},
        path->v());
  }

  template <typename T1, typename T2>
  static std::optional<std::pair<T1, T2>>
  minimum(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            sl->slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
      T2 v = stm::readTVar<T2>(node->value);
      return std::make_optional<std::pair<T1, T2>>(
          std::make_pair(node->key, v));
    } else {
      return std::nullopt;
    }
  }

  template <typename T1, typename T2>
  static std::shared_ptr<TSkipList<T1, T2>> create(const T1 dummyKey,
                                                   const T2 dummyVal) {
    std::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal,
        (((maxLevels - (0 + 1)) > maxLevels ? 0 : (maxLevels - (0 + 1)))));
    std::shared_ptr<stm::TVar<unsigned int>> lvlTV =
        stm::newTVar<unsigned int>(0);
    return std::make_shared<TSkipList<T1, T2>>(
        TSkipList<T1, T2>{headNode, maxLevels, lvlTV});
  }
};

struct skiplist_test {
  static bool nat_lt(const unsigned int, const unsigned int);

  static bool nat_eq(const unsigned int, const unsigned int);

  static bool stm_test_insert_lookup();

  static bool stm_test_delete();

  static bool stm_test_update();

  static bool stm_test_minimum();

  static bool test_insert_lookup();

  static bool test_delete();

  static bool test_update();

  static bool test_minimum();

  static unsigned int run_tests();
};
