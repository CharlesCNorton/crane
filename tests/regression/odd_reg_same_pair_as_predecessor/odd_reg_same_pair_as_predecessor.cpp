#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <odd_reg_same_pair_as_predecessor.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> OddRegSamePairAsPredecessor::regs(
    const std::shared_ptr<OddRegSamePairAsPredecessor::state> &s) {
  return s->regs;
}

unsigned int OddRegSamePairAsPredecessor::get_reg(
    const std::shared_ptr<OddRegSamePairAsPredecessor::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int OddRegSamePairAsPredecessor::get_reg_pair(
    const std::shared_ptr<OddRegSamePairAsPredecessor::state> &s,
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
