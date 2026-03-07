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

std::shared_ptr<List<unsigned int>> AddPreservesAllPairs::regs(
    const std::shared_ptr<AddPreservesAllPairs::state> &s) {
  return s->regs;
}

unsigned int AddPreservesAllPairs::acc(
    const std::shared_ptr<AddPreservesAllPairs::state> &s) {
  return s->acc;
}

unsigned int AddPreservesAllPairs::get_reg(
    const std::shared_ptr<AddPreservesAllPairs::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int AddPreservesAllPairs::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int AddPreservesAllPairs::get_reg_pair(
    const std::shared_ptr<AddPreservesAllPairs::state> &s,
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

std::shared_ptr<AddPreservesAllPairs::state> AddPreservesAllPairs::execute_add(
    std::shared_ptr<AddPreservesAllPairs::state> s, const unsigned int r) {
  return std::make_shared<AddPreservesAllPairs::state>(
      state{s->regs, nibble_of_nat((s->acc + get_reg(s, std::move(r))))});
}
