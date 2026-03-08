#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <inc_modifies_single_nibble_even.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int IncModifiesSingleNibbleEven::get_reg(
    const std::shared_ptr<IncModifiesSingleNibbleEven::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int IncModifiesSingleNibbleEven::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

unsigned int IncModifiesSingleNibbleEven::get_reg_pair(
    const std::shared_ptr<IncModifiesSingleNibbleEven::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<IncModifiesSingleNibbleEven::state>
IncModifiesSingleNibbleEven::execute_inc(
    std::shared_ptr<IncModifiesSingleNibbleEven::state> s,
    const unsigned int r) {
  return std::make_shared<IncModifiesSingleNibbleEven::state>(state{
      update_nth<unsigned int>(r, nibble_of_nat((get_reg(s, r) + 1u)), s->regs),
      s->acc});
}
