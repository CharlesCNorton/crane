#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <psort.h>
#include <string>
#include <utility>
#include <variant>

namespace list {};

namespace sig0 {};

bool le_lt_dec(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      if (le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

std::shared_ptr<list::list<unsigned int>>
merge(const std::shared_ptr<list::list<unsigned int>> l1,
      const std::shared_ptr<list::list<unsigned int>> l2) {
  std::function<std::shared_ptr<list::list<unsigned int>>(
      std::shared_ptr<list::list<unsigned int>>)>
      merge_aux;
  merge_aux = [&](std::shared_ptr<list::list<unsigned int>> l3)
      -> std::shared_ptr<list::list<unsigned int>> {
    return std::visit(
        Overloaded{
            [&](const list::nil<unsigned int> _args)
                -> std::shared_ptr<list::list<unsigned int>> { return l3; },
            [&](const list::cons<unsigned int> _args)
                -> std::shared_ptr<list::list<unsigned int>> {
              unsigned int a1 = _args._a0;
              std::shared_ptr<list::list<unsigned int>> l1_ = _args._a1;
              return std::visit(
                  Overloaded{[&](const list::nil<unsigned int> _args)
                                 -> std::shared_ptr<list::list<unsigned int>> {
                               return l1;
                             },
                             [&](const list::cons<unsigned int> _args)
                                 -> std::shared_ptr<list::list<unsigned int>> {
                               unsigned int a2 = _args._a0;
                               std::shared_ptr<list::list<unsigned int>> l2_ =
                                   _args._a1;
                               if (le_lt_dec(a1, a2)) {
                                 return list::cons<unsigned int>::make(
                                     a1, merge(l1_, l3));
                               } else {
                                 return list::cons<unsigned int>::make(
                                     a2, merge_aux(l2_));
                               }
                             }},
                  *l3);
            }},
        *l1);
  };
  return merge_aux(l2);
}

std::shared_ptr<sig0::sig0<std::shared_ptr<list::list<unsigned int>>>>
pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                const std::shared_ptr<list::list<unsigned int>> _x1,
                const std::shared_ptr<list::list<unsigned int>> l_,
                const std::shared_ptr<list::list<unsigned int>> l_0) {
  return merge(l_0, l_);
}

std::shared_ptr<sig0::sig0<std::shared_ptr<list::list<unsigned int>>>>
psort(const std::shared_ptr<list::list<unsigned int>> _x0) {
  return [&](const std::shared_ptr<list::list<T1>> _x0) {
    return div_conq_pair<unsigned int>(
        list::nil<unsigned int>::make(),
        [&](unsigned int a) {
          return list::cons<unsigned int>::make(
              a, list::nil<unsigned int>::make());
        },
        [&](unsigned int a1, unsigned int a2) {
          bool s = le_lt_dec(a1, a2);
          if (s) {
            return list::cons<unsigned int>::make(
                a1, list::cons<unsigned int>::make(
                        a2, list::nil<unsigned int>::make()));
          } else {
            return list::cons<unsigned int>::make(
                a2, list::cons<unsigned int>::make(
                        a1, list::nil<unsigned int>::make()));
          }
        },
        [&](unsigned int a1, unsigned int a2,
            std::shared_ptr<list::list<unsigned int>> l,
            std::shared_ptr<
                sig0::sig0<std::shared_ptr<list::list<unsigned int>>>>
                x,
            std::shared_ptr<
                sig0::sig0<std::shared_ptr<list::list<unsigned int>>>>
                x0) { return pair_merge_prog(a1, a2, l, x0, x); },
        _x0);
  }(_x0);
}
