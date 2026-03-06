#include <algorithm>
#include <any>
#include <cassert>
#include <decode_jun_wf_edge_0059.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::optional<unsigned int> DecodeJunWfEdge0059::jump_target(
    const std::shared_ptr<DecodeJunWfEdge0059::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename DecodeJunWfEdge0059::instruction::JUN _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename DecodeJunWfEdge0059::instruction::JMS _args)
                     -> std::optional<unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_optional<unsigned int>(std::move(a));
                 },
                 [](const typename DecodeJunWfEdge0059::instruction::NOP _args)
                     -> std::optional<unsigned int> { return std::nullopt; }},
      i->v());
}
