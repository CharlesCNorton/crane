#include <algorithm>
#include <any>
#include <cassert>
#include <execute_inc_wf_edge_0093.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ExecuteIncWfEdge0093::state>
ExecuteIncWfEdge0093::set_prom_params(
    std::shared_ptr<ExecuteIncWfEdge0093::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<ExecuteIncWfEdge0093::state>(
      state{s->acc, s->regs, s->carry, s->pc, s->stack, s->ram_sys, s->cur_bank,
            s->sel_ram, s->rom_ports, s->sel_rom, s->rom, s->test_pin,
            std::move(addr), std::move(data), std::move(enable)});
}
