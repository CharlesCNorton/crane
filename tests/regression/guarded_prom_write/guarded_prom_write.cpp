#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <guarded_prom_write.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<GuardedPromWrite::state>
GuardedPromWrite::execute_wpm(std::shared_ptr<GuardedPromWrite::state> s) {
  if (s->prom_enable_) {
    return std::make_shared<GuardedPromWrite::state>(
        state{update_nth<unsigned int>(s->prom_addr_, s->prom_data_, s->rom_),
              s->prom_addr_, s->prom_data_, s->prom_enable_});
  } else {
    return std::move(s);
  }
}
