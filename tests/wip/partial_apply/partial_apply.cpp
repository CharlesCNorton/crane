#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <partial_apply.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List::list<unsigned int>>
inc_all(const std::shared_ptr<List::list<unsigned int>> &l) {
  return map<unsigned int, unsigned int>([](axiom x) { return (x + 1); }, l);
}

std::shared_ptr<List::list<std::pair<unsigned int, unsigned int>>>
tag_all(const std::shared_ptr<List::list<unsigned int>> &l) {
  return map<unsigned int, std::pair<unsigned int, unsigned int>>(
      [](axiom x) { return std::make_pair((0 + 1), x); }, l);
}

std::shared_ptr<List::list<std::optional<unsigned int>>>
wrap_all(const std::shared_ptr<List::list<unsigned int>> &l) {
  return map<unsigned int, std::optional<unsigned int>>(
      [](axiom x) { return std::make_optional<unsigned int>(x); }, l);
}

std::shared_ptr<List::list<std::shared_ptr<Tagged::tagged<bool>>>>
tag_with(const unsigned int n, const std::shared_ptr<List::list<bool>> &l) {
  return map<bool, std::shared_ptr<Tagged::tagged<bool>>>(
      [&](axiom x) { return Tagged::tagged<bool>::ctor::Tag_(n, x); }, l);
}

unsigned int sum_with_init(const unsigned int init,
                           const std::shared_ptr<List::list<unsigned int>> &l) {
  return fold_left<unsigned int, unsigned int>(
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      },
      l, init);
}
