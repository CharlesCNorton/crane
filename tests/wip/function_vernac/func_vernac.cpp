#include <algorithm>
#include <any>
#include <cassert>
#include <func_vernac.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Sig0::sig0<unsigned int>> div2_terminate(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n1 = n0 - 1;
      return (div2_terminate(n1) + 1);
    }
  }
}

unsigned int div2(const unsigned int _x0) { return div2_terminate(_x0); }

std::shared_ptr<Sig0::sig0<unsigned int>>
list_sum_terminate(const std::shared_ptr<List::list<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List::list<unsigned int>::nil _args)
                     -> std::function<std::shared_ptr<Sig0::sig0<unsigned int>>(
                         dummy_prop)> { return 0; },
                 [](const typename List::list<unsigned int>::cons _args)
                     -> std::function<std::shared_ptr<Sig0::sig0<unsigned int>>(
                         dummy_prop)> {
                   unsigned int n = _args._a0;
                   std::shared_ptr<List::list<unsigned int>> l0 = _args._a1;
                   return (std::move(n) + list_sum_terminate(std::move(l0)));
                 }},
      l->v());
}

unsigned int list_sum(const std::shared_ptr<List::list<unsigned int>> &_x0) {
  return list_sum_terminate(_x0);
}
