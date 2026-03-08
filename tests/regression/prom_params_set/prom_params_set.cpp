#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prom_params_set.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<PromParamsSet::state>
PromParamsSet::set_prom_params(std::shared_ptr<PromParamsSet::state> s,
                               const unsigned int addr, const unsigned int data,
                               const bool enable) {
  return std::make_shared<PromParamsSet::state>(
      state{s->acc, s->regs, s->carry, s->pc, s->stack, s->ram_sys, s->cur_bank,
            s->sel_ram, s->rom_ports, s->sel_rom, s->rom, s->test_pin,
            std::move(addr), std::move(data), std::move(enable)});
}
