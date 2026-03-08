#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_preserves_sel_wf.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<SetPromThenWpmPreservesSelWf::state>
SetPromThenWpmPreservesSelWf::set_prom_params(
    std::shared_ptr<SetPromThenWpmPreservesSelWf::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPreservesSelWf::state>(state{
      s->sel_ram, s->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPreservesSelWf::state>
SetPromThenWpmPreservesSelWf::execute_wpm(
    std::shared_ptr<SetPromThenWpmPreservesSelWf::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPreservesSelWf::state>(
      state{s->sel_ram, std::move(new_rom), s->prom_addr, s->prom_data,
            s->prom_enable});
}
