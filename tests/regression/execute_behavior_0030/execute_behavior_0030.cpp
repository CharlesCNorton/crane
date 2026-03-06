#include <algorithm>
#include <any>
#include <cassert>
#include <execute_behavior_0030.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ExecuteBehavior0030::state> ExecuteBehavior0030::reset_state(
    std::shared_ptr<ExecuteBehavior0030::state> s) {
  return std::make_shared<ExecuteBehavior0030::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
