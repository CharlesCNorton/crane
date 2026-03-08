#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <wpm_writes_exactly_once.h>

std::shared_ptr<WpmWritesExactlyOnce::state> WpmWritesExactlyOnce::execute_wpm(
    std::shared_ptr<WpmWritesExactlyOnce::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<WpmWritesExactlyOnce::state>(
      state{std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}
