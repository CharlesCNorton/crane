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
#include <wpm_disabled_is_nop.h>

std::shared_ptr<WpmDisabledIsNop::state>
WpmDisabledIsNop::execute_wpm(std::shared_ptr<WpmDisabledIsNop::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<WpmDisabledIsNop::state>(
      state{std::move(new_rom), s->prom_addr, s->prom_data, s->prom_enable});
}
