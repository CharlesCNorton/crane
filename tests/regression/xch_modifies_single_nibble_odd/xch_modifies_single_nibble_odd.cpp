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
#include <xch_modifies_single_nibble_odd.h>

std::shared_ptr<List<unsigned int>> XchModifiesSingleNibbleOdd::regs(
    const std::shared_ptr<XchModifiesSingleNibbleOdd::state> &s) {
  return s->regs;
}

unsigned int XchModifiesSingleNibbleOdd::acc(
    const std::shared_ptr<XchModifiesSingleNibbleOdd::state> &s) {
  return s->acc;
}

unsigned int XchModifiesSingleNibbleOdd::get_reg(
    const std::shared_ptr<XchModifiesSingleNibbleOdd::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int XchModifiesSingleNibbleOdd::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int XchModifiesSingleNibbleOdd::get_reg_pair(
    const std::shared_ptr<XchModifiesSingleNibbleOdd::state> &s,
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

std::shared_ptr<XchModifiesSingleNibbleOdd::state>
XchModifiesSingleNibbleOdd::execute_xch(
    std::shared_ptr<XchModifiesSingleNibbleOdd::state> s,
    const unsigned int r) {
  return std::make_shared<XchModifiesSingleNibbleOdd::state>(
      state{update_nth<unsigned int>(r, nibble_of_nat(s->acc), s->regs),
            get_reg(s, r)});
}
