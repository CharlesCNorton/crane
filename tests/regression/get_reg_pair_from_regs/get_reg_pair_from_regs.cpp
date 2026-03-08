#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <get_reg_pair_from_regs.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
GetRegPairFromRegs::get_reg(const std::shared_ptr<GetRegPairFromRegs::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int GetRegPairFromRegs::get_reg_pair(
    const std::shared_ptr<GetRegPairFromRegs::state> &s, const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}
