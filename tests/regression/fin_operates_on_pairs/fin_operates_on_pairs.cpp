#include <algorithm>
#include <any>
#include <cassert>
#include <fin_operates_on_pairs.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>>
FinOperatesOnPairs::regs(const std::shared_ptr<FinOperatesOnPairs::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>>
FinOperatesOnPairs::rom(const std::shared_ptr<FinOperatesOnPairs::state> &s) {
  return s->rom;
}

unsigned int
FinOperatesOnPairs::get_reg(const std::shared_ptr<FinOperatesOnPairs::state> &s,
                            const unsigned int r) {
  return s->regs->nth(r, 0);
}

std::shared_ptr<FinOperatesOnPairs::state>
FinOperatesOnPairs::set_reg(std::shared_ptr<FinOperatesOnPairs::state> s,
                            const unsigned int r, const unsigned int v) {
  return std::make_shared<FinOperatesOnPairs::state>(state{
      update_nth<unsigned int>(
          std::move(r),
          (std::move(v) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          s->regs),
      s->rom});
}

unsigned int FinOperatesOnPairs::get_reg_pair(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r) {
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

std::shared_ptr<FinOperatesOnPairs::state> FinOperatesOnPairs::set_reg_pair(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r,
    const unsigned int v) {
  unsigned int base =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  unsigned int hi = Nat::div(
      v,
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
  unsigned int lo =
      (v % ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1));
  std::shared_ptr<FinOperatesOnPairs::state> s1 =
      set_reg(s, std::move(base), std::move(hi));
  return set_reg(std::move(s1), (std::move(base) + (0 + 1)), std::move(lo));
}

std::shared_ptr<FinOperatesOnPairs::state> FinOperatesOnPairs::execute_fin(
    const std::shared_ptr<FinOperatesOnPairs::state> &s, const unsigned int r) {
  return set_reg_pair(s, r, s->rom->nth(get_reg_pair(s, 0), 0));
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
