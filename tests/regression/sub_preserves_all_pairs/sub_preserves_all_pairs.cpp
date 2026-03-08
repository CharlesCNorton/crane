#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <sub_preserves_all_pairs.h>
#include <utility>
#include <variant>

unsigned int SubPreservesAllPairs::get_reg(
    const std::shared_ptr<SubPreservesAllPairs::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int SubPreservesAllPairs::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

unsigned int SubPreservesAllPairs::get_reg_pair(
    const std::shared_ptr<SubPreservesAllPairs::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<SubPreservesAllPairs::state> SubPreservesAllPairs::execute_sub(
    std::shared_ptr<SubPreservesAllPairs::state> s, const unsigned int r) {
  return std::make_shared<SubPreservesAllPairs::state>(state{
      s->regs, nibble_of_nat((
                   (((s->acc + 16u) - get_reg(s, std::move(r))) > (s->acc + 16u)
                        ? 0
                        : ((s->acc + 16u) - get_reg(s, std::move(r))))))});
}
