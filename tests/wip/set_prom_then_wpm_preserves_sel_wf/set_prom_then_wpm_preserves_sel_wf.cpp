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

unsigned int SetPromThenWpmPreservesSelWf::sel_bank(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::sel> &s) {
  return s->sel_bank;
}

unsigned int SetPromThenWpmPreservesSelWf::sel_chip(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::sel> &s) {
  return s->sel_chip;
}

unsigned int SetPromThenWpmPreservesSelWf::sel_reg(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::sel> &s) {
  return s->sel_reg;
}

std::shared_ptr<SetPromThenWpmPreservesSelWf::sel>
SetPromThenWpmPreservesSelWf::sel_ram(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::state> &s) {
  return s->sel_ram;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesSelWf::rom(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmPreservesSelWf::prom_addr(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmPreservesSelWf::prom_data(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmPreservesSelWf::prom_enable(
    const std::shared_ptr<SetPromThenWpmPreservesSelWf::state> &s) {
  return s->prom_enable;
}

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
