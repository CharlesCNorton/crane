#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <wpm_enabled_preserves_regs.h>

bool WpmEnabledPreservesRegs::nat_list_eqb(
    const std::shared_ptr<List<unsigned int>> &xs,
    const std::shared_ptr<List<unsigned int>> &ys) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::nil _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args) -> bool {
                      return true;
                    },
                    [](const typename List<unsigned int>::cons _args) -> bool {
                      return false;
                    }},
                ys->v());
          },
          [&](const typename List<unsigned int>::cons _args) -> bool {
            unsigned int x = _args._a0;
            std::shared_ptr<List<unsigned int>> xs_ = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args) -> bool {
                      return false;
                    },
                    [&](const typename List<unsigned int>::cons _args) -> bool {
                      unsigned int y = _args._a0;
                      std::shared_ptr<List<unsigned int>> ys_ = _args._a1;
                      return ((std::move(x) == std::move(y)) &&
                              nat_list_eqb(std::move(xs_), std::move(ys_)));
                    }},
                ys->v());
          }},
      xs->v());
}

std::shared_ptr<WpmEnabledPreservesRegs::state>
WpmEnabledPreservesRegs::execute_wpm(
    std::shared_ptr<WpmEnabledPreservesRegs::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<WpmEnabledPreservesRegs::state>(state{
      s->regs, std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}
