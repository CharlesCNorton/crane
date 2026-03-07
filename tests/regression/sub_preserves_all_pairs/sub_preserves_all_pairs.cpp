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

std::shared_ptr<List<unsigned int>> SubPreservesAllPairs::regs(
    const std::shared_ptr<SubPreservesAllPairs::state> &s) {
  return s->regs;
}

unsigned int SubPreservesAllPairs::acc(
    const std::shared_ptr<SubPreservesAllPairs::state> &s) {
  return s->acc;
}

unsigned int SubPreservesAllPairs::get_reg(
    const std::shared_ptr<SubPreservesAllPairs::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int SubPreservesAllPairs::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

unsigned int SubPreservesAllPairs::get_reg_pair(
    const std::shared_ptr<SubPreservesAllPairs::state> &s,
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

std::shared_ptr<SubPreservesAllPairs::state> SubPreservesAllPairs::execute_sub(
    std::shared_ptr<SubPreservesAllPairs::state> s, const unsigned int r) {
  return std::make_shared<SubPreservesAllPairs::state>(state{
      s->regs,
      nibble_of_nat(
          ((((s->acc +
              ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1)) -
             get_reg(s, std::move(r))) >
                    (s->acc +
                     ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1))
                ? 0
                : ((s->acc +
                    ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1)) -
                   get_reg(s, std::move(r))))))});
}
