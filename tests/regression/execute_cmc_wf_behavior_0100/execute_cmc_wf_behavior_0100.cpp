#include <algorithm>
#include <any>
#include <cassert>
#include <execute_cmc_wf_behavior_0100.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ExecuteCmcWfBehavior0100::state>
ExecuteCmcWfBehavior0100::reset_state(
    std::shared_ptr<ExecuteCmcWfBehavior0100::state> s) {
  return std::make_shared<ExecuteCmcWfBehavior0100::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
