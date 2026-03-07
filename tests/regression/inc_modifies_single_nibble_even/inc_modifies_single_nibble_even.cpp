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

std::shared_ptr<List<unsigned int>> IncModifiesSingleNibbleEven::regs(
    const std::shared_ptr<IncModifiesSingleNibbleEven::state> &s) {
  return s->regs;
}

unsigned int IncModifiesSingleNibbleEven::acc(
    const std::shared_ptr<IncModifiesSingleNibbleEven::state> &s) {
  return s->acc;
}

unsigned int IncModifiesSingleNibbleEven::get_reg(
    const std::shared_ptr<IncModifiesSingleNibbleEven::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int IncModifiesSingleNibbleEven::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int IncModifiesSingleNibbleEven::get_reg_pair(
    const std::shared_ptr<IncModifiesSingleNibbleEven::state> &s,
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

std::shared_ptr<IncModifiesSingleNibbleEven::state>
IncModifiesSingleNibbleEven::execute_inc(
    std::shared_ptr<IncModifiesSingleNibbleEven::state> s,
    const unsigned int r) {
  return std::make_shared<IncModifiesSingleNibbleEven::state>(
      state{update_nth<unsigned int>(
                r, nibble_of_nat((get_reg(s, r) + (0 + 1))), s->regs),
            s->acc});
}
