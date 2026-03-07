#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <load_preserves_rom_length.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> LoadPreservesRomLength::rom(
    const std::shared_ptr<LoadPreservesRomLength::state> &s) {
  return s->rom;
}

unsigned int LoadPreservesRomLength::prom_addr(
    const std::shared_ptr<LoadPreservesRomLength::state> &s) {
  return s->prom_addr;
}

unsigned int LoadPreservesRomLength::prom_data(
    const std::shared_ptr<LoadPreservesRomLength::state> &s) {
  return s->prom_data;
}

bool LoadPreservesRomLength::prom_enable(
    const std::shared_ptr<LoadPreservesRomLength::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<LoadPreservesRomLength::state>
LoadPreservesRomLength::set_prom_params(
    std::shared_ptr<LoadPreservesRomLength::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<LoadPreservesRomLength::state>(state{
      std::move(s)->rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<LoadPreservesRomLength::state>
LoadPreservesRomLength::execute_wpm(
    std::shared_ptr<LoadPreservesRomLength::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<LoadPreservesRomLength::state>(
      state{std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}

std::shared_ptr<LoadPreservesRomLength::state>
LoadPreservesRomLength::load_program(
    std::shared_ptr<LoadPreservesRomLength::state> s, const unsigned int base,
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::nil _args)
                     -> std::shared_ptr<LoadPreservesRomLength::state> {
                   return std::move(s);
                 },
                 [&](const typename List<unsigned int>::cons _args)
                     -> std::shared_ptr<LoadPreservesRomLength::state> {
                   unsigned int b = _args._a0;
                   std::shared_ptr<List<unsigned int>> rest = _args._a1;
                   std::shared_ptr<LoadPreservesRomLength::state> s_ =
                       set_prom_params(std::move(s), base, std::move(b), true);
                   std::shared_ptr<LoadPreservesRomLength::state> s__ =
                       execute_wpm(std::move(s_));
                   return load_program(std::move(s__), (base + (0 + 1)),
                                       std::move(rest));
                 }},
      bytes->v());
}
