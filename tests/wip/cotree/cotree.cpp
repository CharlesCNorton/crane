#include <algorithm>
#include <any>
#include <cassert>
#include <cotree.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Colist::colist<unsigned int>> nats(const unsigned int n) {
  return Colist::colist<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Colist::colist<unsigned int>> {
        return Colist::colist<unsigned int>::ctor::cocons_(n, nats((n + 1)));
      });
}

std::shared_ptr<Colist::colist<unsigned int>>
binary_children(const unsigned int n) {
  return Colist::colist<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Colist::colist<unsigned int>> {
        return Colist::colist<unsigned int>::ctor::cocons_(
            ((((0 + 1) + 1) * n) + (0 + 1)),
            Colist::colist<unsigned int>::ctor::cocons_(
                ((((0 + 1) + 1) * n) + ((0 + 1) + 1)),
                Colist::colist<unsigned int>::ctor::conil_()));
      });
}
