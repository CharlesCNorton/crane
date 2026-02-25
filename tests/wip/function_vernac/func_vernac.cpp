#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <func_vernac.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Sig0::sig0<unsigned int>>
FuncVernac::div2_terminate(const unsigned int n) {
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

unsigned int FuncVernac::div2(const unsigned int _x0) {
  return div2_terminate(_x0);
}

std::shared_ptr<FuncVernac::r_div2>
FuncVernac::R_div2_correct(const unsigned int n, const unsigned int _res) {
  return div2_rect([](unsigned int y,
                      unsigned int _x0) { return r_div2::ctor::R_div2_0_(y); },
                   [](unsigned int y, unsigned int _x0) {
                     return r_div2::ctor::R_div2_1_(y);
                   },
                   [](unsigned int y, unsigned int y0,
                      std::function<std::shared_ptr<FuncVernac::r_div2>(
                          unsigned int, dummy_prop)>
                          y2,
                      unsigned int _x0) {
                     return r_div2::ctor::R_div2_2_(y, y0, div2(y0),
                                                    y2(div2(y0), "dummy"));
                   },
                   n, _res, "dummy");
}

std::shared_ptr<Sig0::sig0<unsigned int>> FuncVernac::list_sum_terminate(
    const std::shared_ptr<List::list<unsigned int>> &l) {
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

unsigned int
FuncVernac::list_sum(const std::shared_ptr<List::list<unsigned int>> &_x0) {
  return list_sum_terminate(_x0);
}

std::shared_ptr<FuncVernac::r_list_sum> FuncVernac::R_list_sum_correct(
    const std::shared_ptr<List::list<unsigned int>> &l,
    const unsigned int _res) {
  return list_sum_rect(
      [](std::shared_ptr<List::list<unsigned int>> y, unsigned int _x0) {
        return r_list_sum::ctor::R_list_sum_0_(y);
      },
      [](std::shared_ptr<List::list<unsigned int>> y, unsigned int y0,
         std::shared_ptr<List::list<unsigned int>> y1,
         std::function<std::shared_ptr<FuncVernac::r_list_sum>(unsigned int,
                                                               dummy_prop)>
             y3,
         unsigned int _x0) {
        return r_list_sum::ctor::R_list_sum_1_(y, y0, y1, list_sum(y1),
                                               y3(list_sum(y1), "dummy"));
      },
      l, _res, "dummy");
}
