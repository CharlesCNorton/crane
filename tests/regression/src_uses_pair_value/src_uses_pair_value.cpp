#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <src_uses_pair_value.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
SrcUsesPairValue::regs(const std::shared_ptr<SrcUsesPairValue::state> &s) {
  return s->regs;
}

unsigned int
SrcUsesPairValue::sel_rom(const std::shared_ptr<SrcUsesPairValue::state> &s) {
  return s->sel_rom;
}

unsigned int
SrcUsesPairValue::sel_chip(const std::shared_ptr<SrcUsesPairValue::state> &s) {
  return s->sel_chip;
}

unsigned int
SrcUsesPairValue::sel_reg(const std::shared_ptr<SrcUsesPairValue::state> &s) {
  return s->sel_reg;
}

unsigned int
SrcUsesPairValue::sel_char(const std::shared_ptr<SrcUsesPairValue::state> &s) {
  return s->sel_char;
}

unsigned int
SrcUsesPairValue::get_reg(const std::shared_ptr<SrcUsesPairValue::state> &s,
                          const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int SrcUsesPairValue::get_reg_pair(
    const std::shared_ptr<SrcUsesPairValue::state> &s, const unsigned int r) {
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

std::shared_ptr<SrcUsesPairValue::state>
SrcUsesPairValue::execute_src(std::shared_ptr<SrcUsesPairValue::state> s,
                              const unsigned int r) {
  unsigned int pair_val = get_reg_pair(std::move(s), r);
  unsigned int hi = Nat::div(
      std::move(pair_val),
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
  return std::make_shared<SrcUsesPairValue::state>(state{
      std::move(s)->regs, hi, Nat::div(hi, ((((0 + 1) + 1) + 1) + 1)),
      (hi % ((((0 + 1) + 1) + 1) + 1)),
      (std::move(pair_val) %
       ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1))});
}

std::pair<unsigned int, unsigned int> Nat::divmod(const unsigned int x,
                                                  const unsigned int y,
                                                  const unsigned int q,
                                                  const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

unsigned int Nat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0, y_).first;
  }
}
