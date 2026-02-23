#include <algorithm>
#include <any>
#include <cassert>
#include <comp_proof.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool nat_eq_dec(const unsigned int n, const unsigned int x) {
  if (n <= 0) {
    if (x <= 0) {
      return true;
    } else {
      unsigned int _x = x - 1;
      return false;
    }
  } else {
    unsigned int n0 = n - 1;
    if (x <= 0) {
      return false;
    } else {
      unsigned int n1 = x - 1;
      if (nat_eq_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool nat_eqb_dec(const unsigned int n, const unsigned int m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

bool le_dec(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      bool s = le_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool nat_leb_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

unsigned int min_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return std::move(n);
  } else {
    return std::move(m);
  }
}

unsigned int max_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return std::move(m);
  } else {
    return std::move(n);
  }
}

std::shared_ptr<List::list<unsigned int>>
insert_dec(const unsigned int x,
           const std::shared_ptr<List::list<unsigned int>> &l) {
  return std::visit(
      Overloaded{[&](const typename List::list<unsigned int>::nil _args)
                     -> std::shared_ptr<List::list<unsigned int>> {
                   return List::list<unsigned int>::ctor::cons_(
                       std::move(x), List::list<unsigned int>::ctor::nil_());
                 },
                 [&](const typename List::list<unsigned int>::cons _args)
                     -> std::shared_ptr<List::list<unsigned int>> {
                   unsigned int y = _args._a0;
                   std::shared_ptr<List::list<unsigned int>> rest = _args._a1;
                   if (le_dec(x, y)) {
                     return List::list<unsigned int>::ctor::cons_(
                         std::move(x), List::list<unsigned int>::ctor::cons_(
                                           std::move(y), std::move(rest)));
                   } else {
                     return List::list<unsigned int>::ctor::cons_(
                         std::move(y),
                         insert_dec(std::move(x), std::move(rest)));
                   }
                 }},
      l->v());
}

std::shared_ptr<List::list<unsigned int>>
isort_dec(const std::shared_ptr<List::list<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List::list<unsigned int>::nil _args)
                     -> std::shared_ptr<List::list<unsigned int>> {
                   return List::list<unsigned int>::ctor::nil_();
                 },
                 [](const typename List::list<unsigned int>::cons _args)
                     -> std::shared_ptr<List::list<unsigned int>> {
                   unsigned int x = _args._a0;
                   std::shared_ptr<List::list<unsigned int>> rest = _args._a1;
                   return insert_dec(std::move(x), isort_dec(std::move(rest)));
                 }},
      l->v());
}
