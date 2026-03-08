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

std::shared_ptr<List<unsigned int>> SetRegAffectsPairHigh::regs(
    const std::shared_ptr<SetRegAffectsPairHigh::state> &s) {
  return s->regs;
}

unsigned int SetRegAffectsPairHigh::get_reg(
    const std::shared_ptr<SetRegAffectsPairHigh::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

std::shared_ptr<SetRegAffectsPairHigh::state>
SetRegAffectsPairHigh::set_reg(std::shared_ptr<SetRegAffectsPairHigh::state> s,
                               const unsigned int r, const unsigned int v) {
  return std::make_shared<SetRegAffectsPairHigh::state>(
      state{update_nth<unsigned int>(
          std::move(r),
          (std::move(v) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          std::move(s)->regs)});
}

unsigned int SetRegAffectsPairHigh::get_reg_pair(
    const std::shared_ptr<SetRegAffectsPairHigh::state> &s,
    const unsigned int r) {
  unsigned int base =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  return ((get_reg(s, base) *
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)) +
          get_reg(s, (base + (0 + 1))));
}
