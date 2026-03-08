#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <inc_preserves_pair_partner_odd.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> IncPreservesPairPartnerOdd::regs(
    const std::shared_ptr<IncPreservesPairPartnerOdd::state> &s) {
  return s->regs;
}

unsigned int IncPreservesPairPartnerOdd::acc(
    const std::shared_ptr<IncPreservesPairPartnerOdd::state> &s) {
  return s->acc;
}

unsigned int IncPreservesPairPartnerOdd::get_reg(
    const std::shared_ptr<IncPreservesPairPartnerOdd::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int IncPreservesPairPartnerOdd::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

std::shared_ptr<IncPreservesPairPartnerOdd::state>
IncPreservesPairPartnerOdd::execute_inc(
    std::shared_ptr<IncPreservesPairPartnerOdd::state> s,
    const unsigned int r) {
  return std::make_shared<IncPreservesPairPartnerOdd::state>(
      state{update_nth<unsigned int>(
                r, nibble_of_nat((get_reg(s, r) + (0 + 1))), s->regs),
            s->acc});
}
