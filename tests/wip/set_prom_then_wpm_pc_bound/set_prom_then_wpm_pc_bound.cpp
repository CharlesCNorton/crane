#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_pc_bound.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SetPromThenWpmPcBound::regs(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPcBound::rom(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmPcBound::acc(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->acc;
}

unsigned int SetPromThenWpmPcBound::pc(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPcBound::stack(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->stack;
}

unsigned int SetPromThenWpmPcBound::cur_bank(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->cur_bank;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPcBound::rom_ports(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->rom_ports;
}

unsigned int SetPromThenWpmPcBound::sel_rom(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->sel_rom;
}

unsigned int SetPromThenWpmPcBound::prom_addr(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmPcBound::prom_data(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmPcBound::prom_enable(
    const std::shared_ptr<SetPromThenWpmPcBound::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromThenWpmPcBound::state>
SetPromThenWpmPcBound::set_prom_params(
    std::shared_ptr<SetPromThenWpmPcBound::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPcBound::state>(
      state{s->regs, s->rom, s->acc, s->pc, s->stack, s->cur_bank, s->rom_ports,
            s->sel_rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPcBound::state>
SetPromThenWpmPcBound::execute_wpm(
    std::shared_ptr<SetPromThenWpmPcBound::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPcBound::state>(state{
      s->regs, std::move(new_rom), s->acc, s->pc, s->stack, s->cur_bank,
      s->rom_ports, s->sel_rom, s->prom_addr, s->prom_data, s->prom_enable});
}
