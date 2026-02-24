#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <sprop.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                             const unsigned int y,
                                             const unsigned int q,
                                             const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

unsigned int div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return divmod(x, y_, 0, y_).first;
  }
}

unsigned int guarded_pred(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int m = n - 1;
    return m;
  }
}

unsigned int safe_div(const unsigned int _x0, const unsigned int _x1) {
  return div(_x0, _x1);
}
