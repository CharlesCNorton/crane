#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <ld_preserves_all_pairs.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int LdPreservesAllPairs::get_reg(
    const std::shared_ptr<LdPreservesAllPairs::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int LdPreservesAllPairs::get_reg_pair(
    const std::shared_ptr<LdPreservesAllPairs::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<LdPreservesAllPairs::state>
LdPreservesAllPairs::execute_ld(std::shared_ptr<LdPreservesAllPairs::state> s,
                                const unsigned int r) {
  return std::make_shared<LdPreservesAllPairs::state>(
      state{s->regs, get_reg(s, std::move(r))});
}
