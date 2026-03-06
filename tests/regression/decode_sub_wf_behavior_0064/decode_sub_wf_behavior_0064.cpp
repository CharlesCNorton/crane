#include <algorithm>
#include <any>
#include <cassert>
#include <decode_sub_wf_behavior_0064.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeSubWfBehavior0064::state>
DecodeSubWfBehavior0064::reset_state(
    std::shared_ptr<DecodeSubWfBehavior0064::state> s) {
  return std::make_shared<DecodeSubWfBehavior0064::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
