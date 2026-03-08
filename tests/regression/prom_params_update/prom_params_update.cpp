#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prom_params_update.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<PromParamsUpdate::state>
PromParamsUpdate::set_prom_params(std::shared_ptr<PromParamsUpdate::state> s,
                                  const unsigned int addr,
                                  const unsigned int data, const bool enable) {
  return std::make_shared<PromParamsUpdate::state>(
      state{s->acc, s->regs, s->rom, std::move(addr), std::move(data),
            std::move(enable)});
}
