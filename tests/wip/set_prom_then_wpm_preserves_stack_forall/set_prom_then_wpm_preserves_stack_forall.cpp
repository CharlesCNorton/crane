#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_preserves_stack_forall.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesStackForall::regs(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesStackForall::rom(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmPreservesStackForall::acc(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->acc;
}

unsigned int SetPromThenWpmPreservesStackForall::pc(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesStackForall::stack(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->stack;
}

unsigned int SetPromThenWpmPreservesStackForall::cur_bank(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->cur_bank;
}

std::shared_ptr<List<unsigned int>>
SetPromThenWpmPreservesStackForall::rom_ports(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->rom_ports;
}

unsigned int SetPromThenWpmPreservesStackForall::sel_rom(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->sel_rom;
}

unsigned int SetPromThenWpmPreservesStackForall::prom_addr(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmPreservesStackForall::prom_data(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmPreservesStackForall::prom_enable(
    const std::shared_ptr<SetPromThenWpmPreservesStackForall::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromThenWpmPreservesStackForall::state>
SetPromThenWpmPreservesStackForall::set_prom_params(
    std::shared_ptr<SetPromThenWpmPreservesStackForall::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPreservesStackForall::state>(
      state{s->regs, s->rom, s->acc, s->pc, s->stack, s->cur_bank, s->rom_ports,
            s->sel_rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPreservesStackForall::state>
SetPromThenWpmPreservesStackForall::execute_wpm(
    std::shared_ptr<SetPromThenWpmPreservesStackForall::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPreservesStackForall::state>(state{
      s->regs, std::move(new_rom), s->acc, s->pc, s->stack, s->cur_bank,
      s->rom_ports, s->sel_rom, s->prom_addr, s->prom_data, s->prom_enable});
}
