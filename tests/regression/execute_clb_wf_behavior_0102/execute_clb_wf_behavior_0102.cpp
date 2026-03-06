#include <algorithm>
#include <any>
#include <cassert>
#include <execute_clb_wf_behavior_0102.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ExecuteClbWfBehavior0102::state>
ExecuteClbWfBehavior0102::reset_state(
    std::shared_ptr<ExecuteClbWfBehavior0102::state> s) {
  return std::make_shared<ExecuteClbWfBehavior0102::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
