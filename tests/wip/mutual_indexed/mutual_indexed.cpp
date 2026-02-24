#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mutual_indexed.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int even_val(const unsigned int _x,
                      const std::shared_ptr<EvenTree::evenTree> &t) {
  return std::visit(
      Overloaded{
          [](const typename EvenTree::evenTree::ELeaf _args) -> unsigned int {
            return 0;
          },
          [](const typename EvenTree::evenTree::ENode _args) -> unsigned int {
            unsigned int v = _args._a1;
            return std::move(v);
          }},
      t->v());
}

unsigned int odd_val(const unsigned int _x,
                     const std::shared_ptr<OddTree::oddTree> &t) {
  return std::visit(
      Overloaded{
          [](const typename OddTree::oddTree::ONode _args) -> unsigned int {
            unsigned int v = _args._a1;
            return std::move(v);
          }},
      t->v());
}
