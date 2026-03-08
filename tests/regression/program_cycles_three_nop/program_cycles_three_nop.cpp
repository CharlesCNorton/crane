#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_cycles_three_nop.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ProgramCyclesThreeNop::cycles(
    const std::shared_ptr<ProgramCyclesThreeNop::state> &_x,
    const ProgramCyclesThreeNop::instruction _x0) {
  return 8u;
}

unsigned int ProgramCyclesThreeNop::program_cycles(
    const std::shared_ptr<ProgramCyclesThreeNop::state> &s,
    const std::shared_ptr<List<ProgramCyclesThreeNop::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<ProgramCyclesThreeNop::instruction>::nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<ProgramCyclesThreeNop::instruction>::cons
                  _args) -> unsigned int {
            ProgramCyclesThreeNop::instruction i = _args._a0;
            std::shared_ptr<List<ProgramCyclesThreeNop::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
