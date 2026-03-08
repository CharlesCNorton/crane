#include <algorithm>
#include <any>
#include <cassert>
#include <even_reg_same_pair_as_successor.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> EvenRegSamePairAsSuccessor::regs(
    const std::shared_ptr<EvenRegSamePairAsSuccessor::state> &s) {
  return s->regs;
}

unsigned int EvenRegSamePairAsSuccessor::get_reg(
    const std::shared_ptr<EvenRegSamePairAsSuccessor::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int EvenRegSamePairAsSuccessor::get_reg_pair(
    const std::shared_ptr<EvenRegSamePairAsSuccessor::state> &s,
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
