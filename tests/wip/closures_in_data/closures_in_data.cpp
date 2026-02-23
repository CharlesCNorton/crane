#include <algorithm>
#include <any>
#include <cassert>
#include <closures_in_data.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
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

std::shared_ptr<List::list<unsigned int>> apply_all(
    const std::shared_ptr<List::list<std::function<unsigned int(unsigned int)>>>
        &fns,
    const unsigned int x) {
  return map<std::function<unsigned int(unsigned int)>, unsigned int>(
      [&](std::function<unsigned int(unsigned int)> f) { return f(x); }, fns);
}

unsigned int compose_all(
    const std::shared_ptr<List::list<std::function<unsigned int(unsigned int)>>>
        &fns,
    const unsigned int x) {
  return fold_left<unsigned int, std::function<unsigned int(unsigned int)>>(
      [](unsigned int acc, std::function<unsigned int(unsigned int)> f) {
        return f(acc);
      },
      fns, x);
}

unsigned int
maybe_apply(const std::optional<std::function<unsigned int(unsigned int)>> mf,
            const unsigned int x) {
  if (mf.has_value()) {
    std::function<unsigned int(unsigned int)> f = *mf;
    return std::move(f)(x);
  } else {
    return std::move(x);
  }
}
