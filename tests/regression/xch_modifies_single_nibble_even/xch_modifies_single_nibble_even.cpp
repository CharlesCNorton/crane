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

std::shared_ptr<List<unsigned int>> XchModifiesSingleNibbleEven::regs(
    const std::shared_ptr<XchModifiesSingleNibbleEven::state> &s) {
  return s->regs;
}

unsigned int XchModifiesSingleNibbleEven::acc(
    const std::shared_ptr<XchModifiesSingleNibbleEven::state> &s) {
  return s->acc;
}

unsigned int XchModifiesSingleNibbleEven::get_reg(
    const std::shared_ptr<XchModifiesSingleNibbleEven::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int XchModifiesSingleNibbleEven::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int XchModifiesSingleNibbleEven::get_reg_pair(
    const std::shared_ptr<XchModifiesSingleNibbleEven::state> &s,
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

std::shared_ptr<XchModifiesSingleNibbleEven::state>
XchModifiesSingleNibbleEven::execute_xch(
    std::shared_ptr<XchModifiesSingleNibbleEven::state> s,
    const unsigned int r) {
  return std::make_shared<XchModifiesSingleNibbleEven::state>(
      state{update_nth<unsigned int>(r, nibble_of_nat(s->acc), s->regs),
            get_reg(s, r)});
}
