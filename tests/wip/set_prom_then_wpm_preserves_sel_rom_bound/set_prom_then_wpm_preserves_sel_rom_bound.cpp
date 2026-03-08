#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_preserves_sel_rom_bound.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesSelRomBound::regs(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesSelRomBound::rom(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmPreservesSelRomBound::acc(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->acc;
}

unsigned int SetPromThenWpmPreservesSelRomBound::pc(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesSelRomBound::stack(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->stack;
}

unsigned int SetPromThenWpmPreservesSelRomBound::cur_bank(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->cur_bank;
}

std::shared_ptr<List<unsigned int>>
SetPromThenWpmPreservesSelRomBound::rom_ports(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->rom_ports;
}

unsigned int SetPromThenWpmPreservesSelRomBound::sel_rom(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->sel_rom;
}

unsigned int SetPromThenWpmPreservesSelRomBound::prom_addr(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmPreservesSelRomBound::prom_data(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmPreservesSelRomBound::prom_enable(
    const std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state>
SetPromThenWpmPreservesSelRomBound::set_prom_params(
    std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPreservesSelRomBound::state>(
      state{s->regs, s->rom, s->acc, s->pc, s->stack, s->cur_bank, s->rom_ports,
            s->sel_rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state>
SetPromThenWpmPreservesSelRomBound::execute_wpm(
    std::shared_ptr<SetPromThenWpmPreservesSelRomBound::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPreservesSelRomBound::state>(state{
      s->regs, std::move(new_rom), s->acc, s->pc, s->stack, s->cur_bank,
      s->rom_ports, s->sel_rom, s->prom_addr, s->prom_data, s->prom_enable});
}
