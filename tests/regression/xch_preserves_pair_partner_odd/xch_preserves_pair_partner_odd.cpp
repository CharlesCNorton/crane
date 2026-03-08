#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <xch_preserves_pair_partner_odd.h>

unsigned int XchPreservesPairPartnerOdd::get_reg(
    const std::shared_ptr<XchPreservesPairPartnerOdd::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int XchPreservesPairPartnerOdd::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

std::shared_ptr<XchPreservesPairPartnerOdd::state>
XchPreservesPairPartnerOdd::execute_xch(
    std::shared_ptr<XchPreservesPairPartnerOdd::state> s,
    const unsigned int r) {
  return std::make_shared<XchPreservesPairPartnerOdd::state>(
      state{update_nth<unsigned int>(r, nibble_of_nat(s->acc), s->regs),
            get_reg(s, r)});
}
