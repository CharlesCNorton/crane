#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_reg_affects_pair_high.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int SetRegAffectsPairHigh::get_reg(
    const std::shared_ptr<SetRegAffectsPairHigh::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<SetRegAffectsPairHigh::state>
SetRegAffectsPairHigh::set_reg(std::shared_ptr<SetRegAffectsPairHigh::state> s,
                               const unsigned int r, const unsigned int v) {
  return std::make_shared<SetRegAffectsPairHigh::state>(
      state{update_nth<unsigned int>(std::move(r), (std::move(v) % 16u),
                                     std::move(s)->regs)});
}

unsigned int SetRegAffectsPairHigh::get_reg_pair(
    const std::shared_ptr<SetRegAffectsPairHigh::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}
