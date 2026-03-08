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

unsigned int IncPreservesPairPartnerOdd::get_reg(
    const std::shared_ptr<IncPreservesPairPartnerOdd::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int IncPreservesPairPartnerOdd::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

std::shared_ptr<IncPreservesPairPartnerOdd::state>
IncPreservesPairPartnerOdd::execute_inc(
    std::shared_ptr<IncPreservesPairPartnerOdd::state> s,
    const unsigned int r) {
  return std::make_shared<IncPreservesPairPartnerOdd::state>(state{
      update_nth<unsigned int>(r, nibble_of_nat((get_reg(s, r) + 1u)), s->regs),
      s->acc});
}
