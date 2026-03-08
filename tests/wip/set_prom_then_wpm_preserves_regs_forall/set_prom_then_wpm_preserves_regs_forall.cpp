#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_preserves_regs_forall.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesRegsForall::regs(
    const std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> SetPromThenWpmPreservesRegsForall::rom(
    const std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmPreservesRegsForall::prom_addr(
    const std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmPreservesRegsForall::prom_data(
    const std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmPreservesRegsForall::prom_enable(
    const std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromThenWpmPreservesRegsForall::state>
SetPromThenWpmPreservesRegsForall::set_prom_params(
    std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmPreservesRegsForall::state>(state{
      s->regs, s->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmPreservesRegsForall::state>
SetPromThenWpmPreservesRegsForall::execute_wpm(
    std::shared_ptr<SetPromThenWpmPreservesRegsForall::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmPreservesRegsForall::state>(state{
      s->regs, std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}
