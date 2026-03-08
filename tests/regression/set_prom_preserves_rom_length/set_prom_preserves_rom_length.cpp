#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_preserves_rom_length.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<SetPromPreservesRomLength::state>
SetPromPreservesRomLength::set_prom_params(
    std::shared_ptr<SetPromPreservesRomLength::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<SetPromPreservesRomLength::state>(state{
      std::move(s)->rom, std::move(addr), std::move(data), std::move(enable)});
}
