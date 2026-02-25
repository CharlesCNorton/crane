#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <mutual_indexed.h>
#include <optional>
#include <persistent_array.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
MutualIndexed::even_val(const unsigned int _x,
                        const std::shared_ptr<MutualIndexed::evenTree> &t) {
  return std::visit(
      Overloaded{[](const typename MutualIndexed::evenTree::ELeaf _args)
                     -> unsigned int { return 0; },
                 [](const typename MutualIndexed::evenTree::ENode _args)
                     -> unsigned int {
                   unsigned int v = _args._a1;
                   return std::move(v);
                 }},
      t->v());
}

unsigned int
MutualIndexed::odd_val(const unsigned int _x,
                       const std::shared_ptr<MutualIndexed::oddTree> &t) {
  return std::visit(
      Overloaded{[](const typename MutualIndexed::oddTree::ONode _args)
                     -> unsigned int {
        unsigned int v = _args._a1;
        return std::move(v);
      }},
      t->v());
}
