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
    unsigned int length0() const {
      return std::visit(
          Overloaded{
              [](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (l_->length0() + 1);
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
        std::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        if (ltK(next0->key, target)) {
          return findPred_go<T1, T2>(ltK, fuel_, next0, target, level);
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

  template <typename k, typename v>
  using Pair = std::shared_ptr<SkipNode<k, v>>;

  template <typename K, typename V> struct TSkipList {
    std::shared_ptr<SkipNode<K, V>> slHead;
    unsigned int slMaxLevel;
    std::shared_ptr<stm::TVar<unsigned int>> slLevel;
    std::shared_ptr<stm::TVar<unsigned int>> slLength;
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

  template <typename T1, typename T2>
  static std::shared_ptr<stm::TVar<unsigned int>>
  slLength(const std::shared_ptr<TSkipList<T1, T2>> &t) {
    return t->slLength;
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
    unsigned int have = path->length0();
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
                  std::shared_ptr<SkipNode<T1, T2>> newN =
                      SkipNode<T1, T2>::create(k, v, newLevel);
                  linkNode<T1, T2>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(sl->slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, newLevel)) {
                      return stm::writeTVar<unsigned int>(sl->slLevel,
                                                          newLevel);
                    } else {
                      return;
                    }
                  }();
                  unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
                  return stm::writeTVar<unsigned int>(sl->slLength, (len + 1));
                }
              } else {
                std::shared_ptr<SkipNode<T1, T2>> newN =
                    SkipNode<T1, T2>::create(k, v, newLevel);
                linkNode<T1, T2>(fullPath, newN);
                unsigned int curLvl = stm::readTVar<unsigned int>(sl->slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, newLevel)) {
                    return stm::writeTVar<unsigned int>(sl->slLevel, newLevel);
                  } else {
                    return;
                  }
                }();
                unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
                return stm::writeTVar<unsigned int>(sl->slLength, (len + 1));
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
                  unlinkNode<T1, T2>(fullPath, node);
                  unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
                  return stm::writeTVar<unsigned int>(
                      sl->slLength,
                      (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
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
  static bool isEmpty(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
    return Nat::eqb(len, 0);
  }

  template <typename T1, typename T2>
  static unsigned int length(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    return stm::readTVar<unsigned int>(sl->slLength);
  }

  template <typename T1, typename T2>
  static std::optional<Pair<T1, T2>>
  front(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    return stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        sl->slHead->forward[0]);
  }

  template <typename T1, typename T2>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findLast_aux(const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr) {
    if (fuel <= 0) {
      return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              curr->forward[0]);
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        return findLast_aux<T1, T2>(fuel_, next0);
      } else {
        return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
      }
    }
  }

  template <typename T1, typename T2>
  static std::optional<Pair<T1, T2>>
  back(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            sl->slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<T1, T2>> first = *firstOpt;
      return findLast_aux<T1, T2>(10000u, first);
    } else {
      return std::nullopt;
    }
  }

  template <typename T1, typename T2>
  static void unlinkFirstFromHead(const std::shared_ptr<SkipNode<T1, T2>> head,
                                  const std::shared_ptr<SkipNode<T1, T2>> node,
                                  const unsigned int nodeLevel,
                                  const unsigned int lvl) {
    if (lvl <= 0) {
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              node->forward[0]);
      return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
          head->forward[0], nodeNext);
    } else {
      unsigned int lvl_ = lvl - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> headNext =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              head->forward[lvl]);
      [&](void) {
        if (headNext.has_value()) {
          std::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
          if (Nat::leb(lvl, nodeLevel)) {
            std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
                stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                    node->forward[lvl]);
            return stm::writeTVar<
                std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                head->forward[lvl], nodeNext);
          } else {
            return;
          }
        } else {
          return;
        }
      }();
      return unlinkFirstFromHead<T1, T2>(head, node, nodeLevel, lvl_);
    }
  }

  template <typename T1, typename T2>
  static std::optional<std::pair<T1, T2>>
  popFront(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            sl->slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
      unlinkFirstFromHead<T1, T2>(
          sl->slHead, node, node->level,
          (((maxLevels - (0 + 1)) > maxLevels ? 0 : (maxLevels - (0 + 1)))));
      unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
      stm::writeTVar<unsigned int>(
          sl->slLength, (((len - (0 + 1)) > len ? 0 : (len - (0 + 1)))));
      T2 v = stm::readTVar<T2>(node->value);
      return std::make_optional<std::pair<T1, T2>>(
          std::make_pair(node->key, v));
    } else {
      return std::nullopt;
    }
  }

  template <typename T1, typename T2>
  static void
  unlinkNodeAtAllLevels(const std::shared_ptr<SkipNode<T1, T2>> head,
                        const std::shared_ptr<SkipNode<T1, T2>> node,
                        const unsigned int lvl) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> headNext =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            head->forward[lvl]);
    [&](void) {
      if (headNext.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> _x = *headNext;
        std::optional<std::shared_ptr<SkipNode<T1, T2>>> nodeNext =
            stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                node->forward[lvl]);
        return stm::writeTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            head->forward[lvl], nodeNext);
      } else {
        return;
      }
    }();
    if (lvl <= 0) {
      return;
    } else {
      unsigned int lvl_ = lvl - 1;
      return unlinkNodeAtAllLevels<T1, T2>(head, node, lvl_);
    }
  }

  template <typename T1, typename T2>
  static unsigned int
  removeAll_aux(const unsigned int fuel,
                const std::shared_ptr<SkipNode<T1, T2>> head,
                const unsigned int maxLvl) {
    if (fuel <= 0) {
      return 0;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              head->forward[0]);
      if (firstOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> node = *firstOpt;
        unlinkNodeAtAllLevels<T1, T2>(head, node, maxLvl);
        unsigned int rest = removeAll_aux<T1, T2>(fuel_, head, maxLvl);
        return (rest + 1);
      } else {
        return 0;
      }
    }
  }

  template <typename T1, typename T2>
  static unsigned int removeAll(const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    unsigned int count = removeAll_aux<T1, T2>(
        10000u, sl->slHead,
        (((maxLevels - (0 + 1)) > maxLevels ? 0 : (maxLevels - (0 + 1)))));
    stm::writeTVar<unsigned int>(sl->slLength, 0);
    stm::writeTVar<unsigned int>(sl->slLevel, 0);
    return count;
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static bool addUnique(F0 &&ltK, F1 &&eqK, const T1 k, const T2 v,
                        const std::shared_ptr<TSkipList<T1, T2>> &sl,
                        const unsigned int newLevel) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> fullPath =
        extendPath<T1, T2>(path, sl->slHead, (newLevel + 1));
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> bool { return false; },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args) -> bool {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> existing = *nextOpt;
                if (eqK(existing->key, k)) {
                  return false;
                } else {
                  std::shared_ptr<SkipNode<T1, T2>> newN =
                      SkipNode<T1, T2>::create(k, v, newLevel);
                  linkNode<T1, T2>(fullPath, newN);
                  unsigned int curLvl =
                      stm::readTVar<unsigned int>(sl->slLevel);
                  [&](void) {
                    if (Nat::ltb(curLvl, newLevel)) {
                      return stm::writeTVar<unsigned int>(sl->slLevel,
                                                          newLevel);
                    } else {
                      return;
                    }
                  }();
                  unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
                  stm::writeTVar<unsigned int>(sl->slLength, (len + 1));
                  return true;
                }
              } else {
                std::shared_ptr<SkipNode<T1, T2>> newN =
                    SkipNode<T1, T2>::create(k, v, newLevel);
                linkNode<T1, T2>(fullPath, newN);
                unsigned int curLvl = stm::readTVar<unsigned int>(sl->slLevel);
                [&](void) {
                  if (Nat::ltb(curLvl, newLevel)) {
                    return stm::writeTVar<unsigned int>(sl->slLevel, newLevel);
                  } else {
                    return;
                  }
                }();
                unsigned int len = stm::readTVar<unsigned int>(sl->slLength);
                stm::writeTVar<unsigned int>(sl->slLength, (len + 1));
                return true;
              }
            }},
        fullPath->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static std::optional<Pair<T1, T2>>
  find(F0 &&ltK, F1 &&eqK, const T1 k,
       const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> std::optional<std::shared_ptr<SkipNode<T1, T2>>> {
              return std::nullopt;
            },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args)
                -> std::optional<std::shared_ptr<SkipNode<T1, T2>>> {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
                      node);
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
  static std::optional<Pair<T1, T2>>
  next(const std::shared_ptr<SkipNode<T1, T2>> pair) {
    return stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
        pair->forward[0]);
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::optional<std::shared_ptr<SkipNode<T1, T2>>>
  findPrev_aux(F0 &&eqK, const unsigned int fuel,
               const std::shared_ptr<SkipNode<T1, T2>> curr,
               const std::shared_ptr<SkipNode<T1, T2>> _x, const T1 target) {
    if (fuel <= 0) {
      return std::nullopt;
    } else {
      unsigned int fuel_ = fuel - 1;
      std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
          stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
              curr->forward[0]);
      if (nextOpt.has_value()) {
        std::shared_ptr<SkipNode<T1, T2>> next0 = *nextOpt;
        if (eqK(next0->key, target)) {
          return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(curr);
        } else {
          return findPrev_aux<T1, T2>(eqK, fuel_, next0, curr, target);
        }
      } else {
        return std::nullopt;
      }
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::optional<Pair<T1, T2>>
  previous(F0 &&eqK, const std::shared_ptr<SkipNode<T1, T2>> pair,
           const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::optional<std::shared_ptr<SkipNode<T1, T2>>> firstOpt =
        stm::readTVar<std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
            sl->slHead->forward[0]);
    if (firstOpt.has_value()) {
      std::shared_ptr<SkipNode<T1, T2>> first = *firstOpt;
      if (eqK(first->key, pair->key)) {
        return std::nullopt;
      } else {
        return findPrev_aux<T1, T2>(eqK, 10000u, first, sl->slHead, pair->key);
      }
    } else {
      return std::nullopt;
    }
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0>
  static std::optional<Pair<T1, T2>>
  findLowerBound(F0 &&ltK, const T1 k,
                 const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> std::optional<std::shared_ptr<SkipNode<T1, T2>>> {
              return std::nullopt;
            },
            [](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args)
                -> std::optional<std::shared_ptr<SkipNode<T1, T2>>> {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
                return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
                    node);
              } else {
                return std::nullopt;
              }
            }},
        path->v());
  }

  template <typename T1, typename T2, MapsTo<bool, T1, T1> F0,
            MapsTo<bool, T1, T1> F1>
  static std::optional<Pair<T1, T2>>
  findUpperBound(F0 &&ltK, F1 &&eqK, const T1 k,
                 const std::shared_ptr<TSkipList<T1, T2>> &sl) {
    std::shared_ptr<List::list<std::shared_ptr<SkipNode<T1, T2>>>> path =
        findPath<T1, T2>(ltK, sl, k);
    return std::visit(
        Overloaded{
            [](const typename List::list<std::shared_ptr<SkipNode<T1, T2>>>::nil
                   _args) -> std::optional<std::shared_ptr<SkipNode<T1, T2>>> {
              return std::nullopt;
            },
            [&](const typename List::list<
                std::shared_ptr<SkipNode<T1, T2>>>::cons _args)
                -> std::optional<std::shared_ptr<SkipNode<T1, T2>>> {
              std::shared_ptr<SkipNode<T1, T2>> pred0 = _args._a0;
              std::optional<std::shared_ptr<SkipNode<T1, T2>>> nextOpt =
                  stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      pred0->forward[0]);
              if (nextOpt.has_value()) {
                std::shared_ptr<SkipNode<T1, T2>> node = *nextOpt;
                if (eqK(node->key, k)) {
                  return stm::readTVar<
                      std::optional<std::shared_ptr<SkipNode<T1, T2>>>>(
                      node->forward[0]);
                } else {
                  return std::make_optional<std::shared_ptr<SkipNode<T1, T2>>>(
                      node);
                }
              } else {
                return std::nullopt;
              }
            }},
        path->v());
  }

  template <typename T1, typename T2> static T1 key(const Pair<T1, T2> _x0) {
    return _x0->key;
  }

  template <typename T1, typename T2>
  static std::shared_ptr<TSkipList<T1, T2>> create(const T1 dummyKey,
                                                   const T2 dummyVal) {
    std::shared_ptr<SkipNode<T1, T2>> headNode = SkipNode<T1, T2>::create(
        dummyKey, dummyVal,
        (((maxLevels - (0 + 1)) > maxLevels ? 0 : (maxLevels - (0 + 1)))));
    std::shared_ptr<stm::TVar<unsigned int>> lvlTV =
        stm::newTVar<unsigned int>(0);
    std::shared_ptr<stm::TVar<unsigned int>> lenTV =
        stm::newTVar<unsigned int>(0);
    return std::make_shared<TSkipList<T1, T2>>(
        TSkipList<T1, T2>{headNode, maxLevels, lvlTV, lenTV});
  }
};

struct skiplist_test {
  static bool nat_lt(const unsigned int, const unsigned int);

  static bool nat_eq(const unsigned int, const unsigned int);

  static bool stm_test_insert_lookup();

  static bool stm_test_delete();

  static bool stm_test_update();

  static bool stm_test_minimum();

  static bool stm_test_length_isEmpty();

  static bool stm_test_front_back();

  static bool stm_test_popFront();

  static bool stm_test_addUnique();

  static bool stm_test_find();

  static bool stm_test_navigation();

  static bool stm_test_bounds();

  static bool stm_test_removeAll();

  static bool test_insert_lookup();

  static bool test_delete();

  static bool test_update();

  static bool test_minimum();

  static bool test_length_isEmpty();

  static bool test_front_back();

  static bool test_popFront();

  static bool test_addUnique();

  static bool test_find();

  static bool test_navigation();

  static bool test_bounds();

  static bool test_removeAll();

  static unsigned int run_tests();
};
