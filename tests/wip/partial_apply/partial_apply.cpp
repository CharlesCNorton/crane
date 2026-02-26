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
PartialApply::inc_all(const std::shared_ptr<List::list<unsigned int>> &l) {
  return ListDef::map<unsigned int, unsigned int>(
      [](axiom x) { return (x + 1); }, l);
}

std::shared_ptr<List::list<std::pair<unsigned int, unsigned int>>>
PartialApply::tag_all(const std::shared_ptr<List::list<unsigned int>> &l) {
  return ListDef::map<unsigned int, std::pair<unsigned int, unsigned int>>(
      [](axiom x) { return std::make_pair((0 + 1), x); }, l);
}

std::shared_ptr<List::list<std::optional<unsigned int>>>
PartialApply::wrap_all(const std::shared_ptr<List::list<unsigned int>> &l) {
  return ListDef::map<unsigned int, std::optional<unsigned int>>(
      [](axiom x) { return std::make_optional<unsigned int>(x); }, l);
}

std::shared_ptr<List::list<std::function<std::shared_ptr<
    List::list<unsigned int>>(std::shared_ptr<List::list<unsigned int>>)>>>
PartialApply::prepend_each(const std::shared_ptr<List::list<unsigned int>> &l) {
  return ListDef::map<unsigned int,
                      std::function<std::shared_ptr<List::list<unsigned int>>(
                          std::shared_ptr<List::list<unsigned int>>)>>(
      [](axiom x, axiom x0) {
        return List::list<unsigned int>::ctor::cons_(x, x0);
      },
      l);
}

std::shared_ptr<List::list<std::shared_ptr<PartialApply::tagged<bool>>>>
PartialApply::tag_with(const unsigned int n,
                       const std::shared_ptr<List::list<bool>> &l) {
  return ListDef::map<bool, std::shared_ptr<PartialApply::tagged<bool>>>(
      [&](axiom x) { return tagged<bool>::ctor::Tag_(n, x); }, l);
}

std::shared_ptr<
    List::list<std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>>
PartialApply::double_tag(const std::shared_ptr<List::list<unsigned int>> &l) {
  return ListDef::map<
      unsigned int,
      std::pair<unsigned int, std::pair<unsigned int, unsigned int>>>(
      [](unsigned int x) { return std::make_pair(x, std::make_pair(x, x)); },
      l);
}

unsigned int PartialApply::sum_with_init(
    const unsigned int init,
    const std::shared_ptr<List::list<unsigned int>> &l) {
  return List::fold_left<unsigned int, unsigned int>(
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      },
      l, init);
}
