#include <algorithm>
#include <any>
#include <cassert>
#include <decode_xch_wf_behavior_0066.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeXchWfBehavior0066::state>
DecodeXchWfBehavior0066::reset_state(
    std::shared_ptr<DecodeXchWfBehavior0066::state> s) {
  return std::make_shared<DecodeXchWfBehavior0066::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
