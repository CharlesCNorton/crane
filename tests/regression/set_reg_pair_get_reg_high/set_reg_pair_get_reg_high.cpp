#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_reg_pair_get_reg_high.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int SetRegPairGetRegHigh::get_reg(
    const std::shared_ptr<SetRegPairGetRegHigh::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<SetRegPairGetRegHigh::state>
SetRegPairGetRegHigh::set_reg(std::shared_ptr<SetRegPairGetRegHigh::state> s,
                              const unsigned int r, const unsigned int v) {
  return std::make_shared<SetRegPairGetRegHigh::state>(
      state{update_nth<unsigned int>(std::move(r), (std::move(v) % 16u),
                                     std::move(s)->regs)});
}

std::shared_ptr<SetRegPairGetRegHigh::state> SetRegPairGetRegHigh::set_reg_pair(
    const std::shared_ptr<SetRegPairGetRegHigh::state> &s, const unsigned int r,
    const unsigned int v) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  unsigned int hi = Nat::div(v, 16u);
  unsigned int lo = (v % 16u);
  std::shared_ptr<SetRegPairGetRegHigh::state> s1 =
      set_reg(s, std::move(base), std::move(hi));
  return set_reg(std::move(s1), (std::move(base) + 1u), std::move(lo));
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
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
