#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_prom_data_bound.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SetPromThenWpmPromDataBound::regs(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPromDataBound::rom(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmPromDataBound::acc(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->acc;
}

unsigned int SetPromThenWpmPromDataBound::pc(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPromDataBound::stack(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->stack;
}

unsigned int SetPromThenWpmPromDataBound::cur_bank(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->cur_bank;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPromDataBound::rom_ports(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->rom_ports;
}

unsigned int SetPromThenWpmPromDataBound::sel_rom(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->sel_rom;
}

unsigned int SetPromThenWpmPromDataBound::prom_addr(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmPromDataBound::prom_data(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmPromDataBound::prom_enable(
    const std::shared_ptr<SetPromThenWpmPromDataBound::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromThenWpmPromDataBound::state>
SetPromThenWpmPromDataBound::set_prom_params(
    std::shared_ptr<SetPromThenWpmPromDataBound::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPromDataBound::state>(
      state{s->regs, s->rom, s->acc, s->pc, s->stack, s->cur_bank, s->rom_ports,
            s->sel_rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPromDataBound::state>
SetPromThenWpmPromDataBound::execute_wpm(
    std::shared_ptr<SetPromThenWpmPromDataBound::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPromDataBound::state>(state{
      s->regs, std::move(new_rom), s->acc, s->pc, s->stack, s->cur_bank,
      s->rom_ports, s->sel_rom, s->prom_addr, s->prom_data, s->prom_enable});
}
