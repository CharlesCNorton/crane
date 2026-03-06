#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <reset_state_carry_clear.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<ResetStateCarryClear::state> ResetStateCarryClear::reset_state(
    std::shared_ptr<ResetStateCarryClear::state> s) {
  return std::make_shared<ResetStateCarryClear::state>(
      state{s->regs, false, 0, s->ram_sys, s->rom});
}
