#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <program_cycles_single.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ProgramCyclesSingle::cycles(
    const std::shared_ptr<ProgramCyclesSingle::state> &_x,
    const ProgramCyclesSingle::instruction _x0) {
  return 8u;
}

unsigned int ProgramCyclesSingle::program_cycles(
    const std::shared_ptr<ProgramCyclesSingle::state> &s,
    const std::shared_ptr<List<ProgramCyclesSingle::instruction>> &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<ProgramCyclesSingle::instruction>::nil _args)
              -> unsigned int { return 0u; },
          [&](const typename List<ProgramCyclesSingle::instruction>::cons _args)
              -> unsigned int {
            ProgramCyclesSingle::instruction i = _args._a0;
            std::shared_ptr<List<ProgramCyclesSingle::instruction>> rest =
                _args._a1;
            return (cycles(s, i) + program_cycles(s, std::move(rest)));
          }},
      prog->v());
}
