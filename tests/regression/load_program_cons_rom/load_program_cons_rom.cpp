#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <load_program_cons_rom.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
LoadProgramConsRom::rom(const std::shared_ptr<LoadProgramConsRom::state> &s) {
  return s->rom;
}

unsigned int LoadProgramConsRom::prom_addr(
    const std::shared_ptr<LoadProgramConsRom::state> &s) {
  return s->prom_addr;
}

unsigned int LoadProgramConsRom::prom_data(
    const std::shared_ptr<LoadProgramConsRom::state> &s) {
  return s->prom_data;
}

bool LoadProgramConsRom::prom_enable(
    const std::shared_ptr<LoadProgramConsRom::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<LoadProgramConsRom::state> LoadProgramConsRom::set_prom_params(
    std::shared_ptr<LoadProgramConsRom::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<LoadProgramConsRom::state>(state{
      std::move(s)->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<LoadProgramConsRom::state>
LoadProgramConsRom::execute_wpm(std::shared_ptr<LoadProgramConsRom::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<LoadProgramConsRom::state>(
      state{std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}

std::shared_ptr<LoadProgramConsRom::state> LoadProgramConsRom::load_program(
    std::shared_ptr<LoadProgramConsRom::state> s, const unsigned int base,
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::shared_ptr<LoadProgramConsRom::state> {
                   return std::move(s);
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::shared_ptr<LoadProgramConsRom::state> {
                   unsigned int b = _args._a0;
                   std::shared_ptr<List<unsigned int>> rest = _args._a1;
                   std::shared_ptr<LoadProgramConsRom::state> s_ =
                       set_prom_params(std::move(s), base, std::move(b), true);
                   std::shared_ptr<LoadProgramConsRom::state> s__ =
                       execute_wpm(std::move(s_));
                   return load_program(std::move(s__), (base + (0 + 1)),
                                       std::move(rest));
                 }},
      bytes->v());
}
