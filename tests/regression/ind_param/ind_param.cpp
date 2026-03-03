#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <ind_param.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int IndParam::NatContainer::size(
    const std::shared_ptr<IndParam::NatContainer::t> &c) {
  return std::visit(
      Overloaded{[](const typename IndParam::NatContainer::t::Empty _args)
                     -> unsigned int { return 0; },
                 [](const typename IndParam::NatContainer::t::Single _args)
                     -> unsigned int { return (0 + 1); },
                 [](const typename IndParam::NatContainer::t::Pair _args)
                     -> unsigned int { return ((0 + 1) + 1); }},
      c->v());
}
