#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_reg_pair_high_nibble.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int SetRegPairHighNibble::get_reg(
    const std::shared_ptr<SetRegPairHighNibble::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0u);
}

std::shared_ptr<List<unsigned int>>
SetRegPairHighNibble::update_nth_nat(const unsigned int n, const unsigned int x,
                                     std::shared_ptr<List<unsigned int>> l) {
  if ((n < l->length())) {
    return l->firstn(n)->app(
        List<unsigned int>::ctor::cons_(std::move(x), l->skipn((n + 1))));
  } else {
    return std::move(l);
  }
}

std::shared_ptr<SetRegPairHighNibble::state> SetRegPairHighNibble::set_reg_pair(
    std::shared_ptr<SetRegPairHighNibble::state> s, const unsigned int r,
    const unsigned int v) {
  unsigned int base = (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
  unsigned int hi = Nat::div(v, 16u);
  unsigned int lo = (v % 16u);
  return std::make_shared<SetRegPairHighNibble::state>(state{
      update_nth_nat((base + 1u), std::move(lo),
                     update_nth_nat(base, std::move(hi), std::move(s)->regs))});
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
