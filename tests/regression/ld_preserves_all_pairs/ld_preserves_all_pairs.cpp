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

std::shared_ptr<List<unsigned int>> LdPreservesAllPairs::regs(
    const std::shared_ptr<LdPreservesAllPairs::state> &s) {
  return s->regs;
}

unsigned int
LdPreservesAllPairs::acc(const std::shared_ptr<LdPreservesAllPairs::state> &s) {
  return s->acc;
}

unsigned int LdPreservesAllPairs::get_reg(
    const std::shared_ptr<LdPreservesAllPairs::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int LdPreservesAllPairs::get_reg_pair(
    const std::shared_ptr<LdPreservesAllPairs::state> &s,
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

std::shared_ptr<LdPreservesAllPairs::state>
LdPreservesAllPairs::execute_ld(std::shared_ptr<LdPreservesAllPairs::state> s,
                                const unsigned int r) {
  return std::make_shared<LdPreservesAllPairs::state>(
      state{s->regs, get_reg(s, std::move(r))});
}
