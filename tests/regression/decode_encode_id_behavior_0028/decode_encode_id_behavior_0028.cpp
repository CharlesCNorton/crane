#include <algorithm>
#include <any>
#include <cassert>
#include <decode_encode_id_behavior_0028.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeEncodeIdBehavior0028::state>
DecodeEncodeIdBehavior0028::reset_state(
    std::shared_ptr<DecodeEncodeIdBehavior0028::state> s) {
  return std::make_shared<DecodeEncodeIdBehavior0028::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
