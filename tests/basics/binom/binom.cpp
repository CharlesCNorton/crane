#include <algorithm>
#include <binom.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

namespace list {};

namespace Binom {
namespace tree {
std::shared_ptr<tree> Node::make(key _a0, std::shared_ptr<tree> _a1,
                                 std::shared_ptr<tree> _a2) {
  return std::make_shared<tree>(Node{_a0, _a1, _a2});
}
std::shared_ptr<tree> Leaf::make() { return std::make_shared<tree>(Leaf{}); }
}; // namespace tree

std::shared_ptr<tree::tree> smash(const std::shared_ptr<tree::tree> t,
                                  const std::shared_ptr<tree::tree> u) {
  return std::visit(
      Overloaded{
          [&](const tree::Node _args) -> std::shared_ptr<tree::tree> {
            unsigned int x = _args._a0;
            std::shared_ptr<tree::tree> t1 = _args._a1;
            std::shared_ptr<tree::tree> t0 = _args._a2;
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args) -> std::shared_ptr<tree::tree> {
                      return tree::Leaf::make();
                    },
                    [&](const tree::Leaf _args) -> std::shared_ptr<tree::tree> {
                      return std::visit(
                          Overloaded{
                              [&](const tree::Node _args)
                                  -> std::shared_ptr<tree::tree> {
                                unsigned int y = _args._a0;
                                std::shared_ptr<tree::tree> u1 = _args._a1;
                                std::shared_ptr<tree::tree> t2 = _args._a2;
                                return std::visit(
                                    Overloaded{
                                        [&](const tree::Node _args)
                                            -> std::shared_ptr<tree::tree> {
                                          return tree::Leaf::make();
                                        },
                                        [&](const tree::Leaf _args)
                                            -> std::shared_ptr<tree::tree> {
                                          if ((y < x)) {
                                            return tree::Node::make(
                                                x, tree::Node::make(y, u1, t1),
                                                tree::Leaf::make());
                                          } else {
                                            return tree::Node::make(
                                                y, tree::Node::make(x, t1, u1),
                                                tree::Leaf::make());
                                          }
                                        }},
                                    *t2);
                              },
                              [&](const tree::Leaf _args)
                                  -> std::shared_ptr<tree::tree> {
                                return tree::Leaf::make();
                              }},
                          *u);
                    }},
                *t0);
          },
          [&](const tree::Leaf _args) -> std::shared_ptr<tree::tree> {
            return tree::Leaf::make();
          }},
      *t);
}

std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>
carry(const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q,
      const std::shared_ptr<tree::tree> t) {
  return std::visit(
      Overloaded{
          [&](const list::nil<std::shared_ptr<tree::tree>> _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return list::cons<std::shared_ptr<tree::tree>>::make(
                          t, list::nil<std::shared_ptr<tree::tree>>::make());
                    },
                    [&](const tree::Leaf _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return list::nil<std::shared_ptr<tree::tree>>::make();
                    }},
                *t);
          },
          [&](const list::cons<std::shared_ptr<tree::tree>> _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            std::shared_ptr<tree::tree> u = _args._a0;
            std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q_ =
                _args._a1;
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const tree::Node _args)
                                  -> std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>> {
                                return list::cons<std::shared_ptr<tree::tree>>::
                                    make(tree::Leaf::make(),
                                         carry(q_, smash(t, u)));
                              },
                              [&](const tree::Leaf _args)
                                  -> std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>> {
                                return list::cons<
                                    std::shared_ptr<tree::tree>>::make(u, q_);
                              }},
                          *t);
                    },
                    [&](const tree::Leaf _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return list::cons<std::shared_ptr<tree::tree>>::make(t,
                                                                           q_);
                    }},
                *u);
          }},
      *q);
}

priqueue
insert(const unsigned int x,
       const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q) {
  return carry(q, tree::Node::make(x, tree::Leaf::make(), tree::Leaf::make()));
}

priqueue join(const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> p,
              const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q,
              const std::shared_ptr<tree::tree> c) {
  return std::visit(
      Overloaded{
          [&](const list::nil<std::shared_ptr<tree::tree>> _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            return carry(q, c);
          },
          [&](const list::cons<std::shared_ptr<tree::tree>> _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            std::shared_ptr<tree::tree> p1 = _args._a0;
            std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> p_ =
                _args._a1;
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const list::nil<std::shared_ptr<tree::tree>>
                                      _args)
                                  -> std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>> {
                                return carry(p, c);
                              },
                              [&](const list::cons<std::shared_ptr<tree::tree>>
                                      _args)
                                  -> std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>> {
                                std::shared_ptr<tree::tree> q1 = _args._a0;
                                std::shared_ptr<
                                    list::list<std::shared_ptr<tree::tree>>>
                                    q_ = _args._a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const tree::Node _args)
                                            -> std::shared_ptr<list::list<
                                                std::shared_ptr<tree::tree>>> {
                                          return list::cons<std::shared_ptr<
                                              tree::tree>>::make(c,
                                                                 join(p_, q_,
                                                                      smash(
                                                                          p1,
                                                                          q1)));
                                        },
                                        [&](const tree::Leaf _args)
                                            -> std::shared_ptr<list::list<
                                                std::shared_ptr<tree::tree>>> {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const tree::Node _args)
                                                      -> std::shared_ptr<
                                                          list::list<
                                                              std::shared_ptr<
                                                                  tree::
                                                                      tree>>> {
                                                    return list::cons<
                                                        std::shared_ptr<
                                                            tree::tree>>::
                                                        make(
                                                            tree::Leaf::make(),
                                                            join(p_, q_,
                                                                 smash(c, p1)));
                                                  },
                                                  [&](const tree::Leaf _args)
                                                      -> std::shared_ptr<
                                                          list::list<
                                                              std::shared_ptr<
                                                                  tree::
                                                                      tree>>> {
                                                    return list::cons<
                                                        std::shared_ptr<
                                                            tree::tree>>::
                                                        make(p1,
                                                             join(p_, q_,
                                                                  tree::Leaf::
                                                                      make()));
                                                  }},
                                              *c);
                                        }},
                                    *q1);
                              }},
                          *q);
                    },
                    [&](const tree::Leaf _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const list::nil<std::shared_ptr<tree::tree>>
                                      _args)
                                  -> std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>> {
                                return carry(p, c);
                              },
                              [&](const list::cons<std::shared_ptr<tree::tree>>
                                      _args)
                                  -> std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>> {
                                std::shared_ptr<tree::tree> q1 = _args._a0;
                                std::shared_ptr<
                                    list::list<std::shared_ptr<tree::tree>>>
                                    q_ = _args._a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const tree::Node _args)
                                            -> std::shared_ptr<list::list<
                                                std::shared_ptr<tree::tree>>> {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const tree::Node _args)
                                                      -> std::shared_ptr<
                                                          list::list<
                                                              std::shared_ptr<
                                                                  tree::
                                                                      tree>>> {
                                                    return list::cons<
                                                        std::shared_ptr<
                                                            tree::tree>>::
                                                        make(
                                                            tree::Leaf::make(),
                                                            join(p_, q_,
                                                                 smash(c, q1)));
                                                  },
                                                  [&](const tree::Leaf _args)
                                                      -> std::shared_ptr<
                                                          list::list<
                                                              std::shared_ptr<
                                                                  tree::
                                                                      tree>>> {
                                                    return list::cons<
                                                        std::shared_ptr<
                                                            tree::tree>>::
                                                        make(q1,
                                                             join(p_, q_,
                                                                  tree::Leaf::
                                                                      make()));
                                                  }},
                                              *c);
                                        },
                                        [&](const tree::Leaf _args)
                                            -> std::shared_ptr<list::list<
                                                std::shared_ptr<tree::tree>>> {
                                          return list::cons<
                                              std::shared_ptr<tree::tree>>::
                                              make(c, join(p_, q_,
                                                           tree::Leaf::make()));
                                        }},
                                    *q1);
                              }},
                          *q);
                    }},
                *p1);
          }},
      *p);
}

priqueue heap_delete_max(const std::shared_ptr<tree::tree> t) {
  return std::visit(
      Overloaded{
          [&](const tree::Node _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            std::shared_ptr<tree::tree> t1 = _args._a1;
            std::shared_ptr<tree::tree> t0 = _args._a2;
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return list::nil<std::shared_ptr<tree::tree>>::make();
                    },
                    [&](const tree::Leaf _args)
                        -> std::shared_ptr<
                            list::list<std::shared_ptr<tree::tree>>> {
                      return unzip(t1,
                                   [&](std::shared_ptr<
                                       list::list<std::shared_ptr<tree::tree>>>
                                           u) { return u; });
                    }},
                *t0);
          },
          [&](const tree::Leaf _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            return list::nil<std::shared_ptr<tree::tree>>::make();
          }},
      *t);
}

key find_max_helper(
    const unsigned int current,
    const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q) {
  return std::visit(
      Overloaded{[&](const list::nil<std::shared_ptr<tree::tree>> _args)
                     -> unsigned int { return current; },
                 [&](const list::cons<std::shared_ptr<tree::tree>> _args)
                     -> unsigned int {
                   std::shared_ptr<tree::tree> t = _args._a0;
                   std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q_ =
                       _args._a1;
                   return std::visit(
                       Overloaded{[&](const tree::Node _args) -> unsigned int {
                                    unsigned int x = _args._a0;
                                    return find_max_helper(
                                        [&](void) {
                                          if ((current < x)) {
                                            return x;
                                          } else {
                                            return current;
                                          }
                                        }(),
                                        q_);
                                  },
                                  [&](const tree::Leaf _args) -> unsigned int {
                                    return find_max_helper(current, q_);
                                  }},
                       *t);
                 }},
      *q);
}

std::optional<key>
find_max(const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q) {
  return std::visit(
      Overloaded{
          [&](const list::nil<std::shared_ptr<tree::tree>> _args)
              -> std::optional<unsigned int> { return std::nullopt; },
          [&](const list::cons<std::shared_ptr<tree::tree>> _args)
              -> std::optional<unsigned int> {
            std::shared_ptr<tree::tree> t = _args._a0;
            std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q_ =
                _args._a1;
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args) -> std::optional<unsigned int> {
                      unsigned int x = _args._a0;
                      return std::make_optional<unsigned int>(
                          find_max_helper(x, q_));
                    },
                    [&](const tree::Leaf _args) -> std::optional<unsigned int> {
                      return find_max(q_);
                    }},
                *t);
          }},
      *q);
}

std::pair<priqueue, priqueue> delete_max_aux(
    const unsigned int m,
    const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> p) {
  return std::visit(
      Overloaded{
          [&](const list::nil<std::shared_ptr<tree::tree>> _args)
              -> std::pair<
                  std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>,
                  std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>> {
            return std::make_pair(
                list::nil<std::shared_ptr<tree::tree>>::make(),
                list::nil<std::shared_ptr<tree::tree>>::make());
          },
          [&](const list::cons<std::shared_ptr<tree::tree>> _args)
              -> std::pair<
                  std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>,
                  std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>> {
            std::shared_ptr<tree::tree> t = _args._a0;
            std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> p_ =
                _args._a1;
            return std::visit(
                Overloaded{
                    [&](const tree::Node _args)
                        -> std::pair<
                            std::shared_ptr<
                                list::list<std::shared_ptr<tree::tree>>>,
                            std::shared_ptr<
                                list::list<std::shared_ptr<tree::tree>>>> {
                      unsigned int x = _args._a0;
                      std::shared_ptr<tree::tree> t1 = _args._a1;
                      std::shared_ptr<tree::tree> t0 = _args._a2;
                      return std::visit(
                          Overloaded{
                              [&](const tree::Node _args)
                                  -> std::pair<
                                      std::shared_ptr<list::list<
                                          std::shared_ptr<tree::tree>>>,
                                      std::shared_ptr<list::list<
                                          std::shared_ptr<tree::tree>>>> {
                                return std::make_pair(
                                    list::nil<
                                        std::shared_ptr<tree::tree>>::make(),
                                    list::nil<
                                        std::shared_ptr<tree::tree>>::make());
                              },
                              [&](const tree::Leaf _args)
                                  -> std::pair<
                                      std::shared_ptr<list::list<
                                          std::shared_ptr<tree::tree>>>,
                                      std::shared_ptr<list::list<
                                          std::shared_ptr<tree::tree>>>> {
                                if ((x < m)) {
                                  std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>>
                                      j = delete_max_aux(m, p_).first;
                                  std::shared_ptr<
                                      list::list<std::shared_ptr<tree::tree>>>
                                      k = delete_max_aux(m, p_).second;
                                  return std::make_pair(
                                      list::cons<std::shared_ptr<tree::tree>>::
                                          make(tree::Node::make(
                                                   x, t1, tree::Leaf::make()),
                                               j),
                                      k);
                                } else {
                                  return std::make_pair(
                                      list::cons<std::shared_ptr<tree::tree>>::
                                          make(tree::Leaf::make(), p_),
                                      heap_delete_max(tree::Node::make(
                                          x, t1, tree::Leaf::make())));
                                }
                              }},
                          *t0);
                    },
                    [&](const tree::Leaf _args)
                        -> std::pair<
                            std::shared_ptr<
                                list::list<std::shared_ptr<tree::tree>>>,
                            std::shared_ptr<
                                list::list<std::shared_ptr<tree::tree>>>> {
                      std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>
                          j = delete_max_aux(m, p_).first;
                      std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>
                          k = delete_max_aux(m, p_).second;
                      return std::make_pair(
                          list::cons<std::shared_ptr<tree::tree>>::make(
                              tree::Leaf::make(), j),
                          k);
                    }},
                *t);
          }},
      *p);
}

std::optional<std::pair<key, priqueue>>
delete_max(const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q) {
  if (find_max(q).has_value()) {
    unsigned int m = *find_max(q);
    std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> p_ =
        delete_max_aux(m, q).first;
    std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q_ =
        delete_max_aux(m, q).second;
    return std::make_optional<
        std::pair<unsigned int,
                  std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>>>(
        std::make_pair(m, join(p_, q_, tree::Leaf::make())));
  } else {
    return std::nullopt;
  }
}

priqueue
merge(const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> p,
      const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q) {
  return join(p, q, tree::Leaf::make());
}

priqueue
insert_list(const std::shared_ptr<list::list<unsigned int>> l,
            const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> q) {
  return std::visit(
      Overloaded{
          [&](const list::nil<unsigned int> _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            return q;
          },
          [&](const list::cons<unsigned int> _args)
              -> std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> {
            unsigned int x = _args._a0;
            std::shared_ptr<list::list<unsigned int>> l0 = _args._a1;
            return insert_list(l0, insert(x, q));
          }},
      *l);
}

std::shared_ptr<list::list<unsigned int>>
make_list(const unsigned int n,
          const std::shared_ptr<list::list<unsigned int>> l) {
  if (n <= 0) {
    return list::cons<unsigned int>::make(0, l);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return list::cons<unsigned int>::make((0 + 1), l);
    } else {
      unsigned int n1 = n0 - 1;
      return make_list(n1, list::cons<unsigned int>::make(((n1 + 1) + 1), l));
    }
  }
}

key help(const std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> c) {
  if (delete_max(c).has_value()) {
    std::pair<unsigned int,
              std::shared_ptr<list::list<std::shared_ptr<tree::tree>>>>
        p = *delete_max(c);
    unsigned int k = p.first;
    std::shared_ptr<list::list<std::shared_ptr<tree::tree>>> _x = p.second;
    return k;
  } else {
    return 0;
  }
}

}; // namespace Binom
