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
#include <xch_modifies_single_nibble_even.h>

unsigned int XchModifiesSingleNibbleEven::get_reg(
    const std::shared_ptr<XchModifiesSingleNibbleEven::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int XchModifiesSingleNibbleEven::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

unsigned int XchModifiesSingleNibbleEven::get_reg_pair(
    const std::shared_ptr<XchModifiesSingleNibbleEven::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<XchModifiesSingleNibbleEven::state>
XchModifiesSingleNibbleEven::execute_xch(
    std::shared_ptr<XchModifiesSingleNibbleEven::state> s,
    const unsigned int r) {
  return std::make_shared<XchModifiesSingleNibbleEven::state>(
      state{update_nth<unsigned int>(r, nibble_of_nat(s->acc), s->regs),
            get_reg(s, r)});
}
