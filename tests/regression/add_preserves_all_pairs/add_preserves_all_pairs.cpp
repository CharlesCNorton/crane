#include <add_preserves_all_pairs.h>
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

unsigned int AddPreservesAllPairs::get_reg(
    const std::shared_ptr<AddPreservesAllPairs::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

unsigned int AddPreservesAllPairs::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

unsigned int AddPreservesAllPairs::get_reg_pair(
    const std::shared_ptr<AddPreservesAllPairs::state> &s,
    const unsigned int r) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  return ((get_reg(s, base) * 16u) + get_reg(s, (base + 1u)));
}

std::shared_ptr<AddPreservesAllPairs::state> AddPreservesAllPairs::execute_add(
    std::shared_ptr<AddPreservesAllPairs::state> s, const unsigned int r) {
  return std::make_shared<AddPreservesAllPairs::state>(
      state{s->regs, nibble_of_nat((s->acc + get_reg(s, std::move(r))))});
}
