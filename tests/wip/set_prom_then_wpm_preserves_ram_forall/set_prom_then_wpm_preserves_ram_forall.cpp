#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_preserves_ram_forall.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<SetPromThenWpmPreservesRamForall::state>
SetPromThenWpmPreservesRamForall::set_prom_params(
    std::shared_ptr<SetPromThenWpmPreservesRamForall::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPreservesRamForall::state>(state{
      s->ram_sys, s->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPreservesRamForall::state>
SetPromThenWpmPreservesRamForall::execute_wpm(
    std::shared_ptr<SetPromThenWpmPreservesRamForall::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPreservesRamForall::state>(
      state{s->ram_sys, std::move(new_rom), s->prom_addr, s->prom_data,
            s->prom_enable});
}
