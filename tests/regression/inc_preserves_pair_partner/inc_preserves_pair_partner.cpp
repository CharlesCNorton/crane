#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <inc_preserves_pair_partner.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> IncPreservesPairPartner::regs(
    const std::shared_ptr<IncPreservesPairPartner::state> &s) {
  return s->regs;
}

unsigned int IncPreservesPairPartner::acc(
    const std::shared_ptr<IncPreservesPairPartner::state> &s) {
  return s->acc;
}

unsigned int IncPreservesPairPartner::get_reg(
    const std::shared_ptr<IncPreservesPairPartner::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int IncPreservesPairPartner::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

std::shared_ptr<IncPreservesPairPartner::state>
IncPreservesPairPartner::execute_inc(
    std::shared_ptr<IncPreservesPairPartner::state> s, const unsigned int r) {
  return std::make_shared<IncPreservesPairPartner::state>(
      state{update_nth<unsigned int>(
                r, nibble_of_nat((get_reg(s, r) + (0 + 1))), s->regs),
            s->acc});
}
