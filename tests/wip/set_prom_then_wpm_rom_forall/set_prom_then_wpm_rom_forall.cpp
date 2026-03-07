#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm_rom_forall.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> SetPromThenWpmRomForall::rom(
    const std::shared_ptr<SetPromThenWpmRomForall::state> &s) {
  return s->rom;
}

unsigned int SetPromThenWpmRomForall::prom_addr(
    const std::shared_ptr<SetPromThenWpmRomForall::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromThenWpmRomForall::prom_data(
    const std::shared_ptr<SetPromThenWpmRomForall::state> &s) {
  return s->prom_data;
}

bool SetPromThenWpmRomForall::prom_enable(
    const std::shared_ptr<SetPromThenWpmRomForall::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromThenWpmRomForall::state>
SetPromThenWpmRomForall::set_prom_params(
    std::shared_ptr<SetPromThenWpmRomForall::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpmRomForall::state>(state{
      std::move(s)->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpmRomForall::state>
SetPromThenWpmRomForall::execute_wpm(
    std::shared_ptr<SetPromThenWpmRomForall::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpmRomForall::state>(
      state{std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}
