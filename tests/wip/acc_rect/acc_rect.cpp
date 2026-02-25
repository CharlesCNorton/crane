#include <acc_rect.h>
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

unsigned int Nat::sub(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return std::move(n);
  } else {
    unsigned int k = n - 1;
    if (m <= 0) {
      return n;
    } else {
      unsigned int l = m - 1;
      return sub(std::move(k), l);
    }
  }
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
      return divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

unsigned int Nat::modulo(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(x);
  } else {
    unsigned int y_ = y - 1;
    return sub(y_, divmod(x, y_, 0, y_).second);
  }
}

std::shared_ptr<List::list<unsigned int>>
AccRect::countdown_acc(const unsigned int n) {
  if (n <= 0) {
    return List::list<unsigned int>::ctor::cons_(
        0, List::list<unsigned int>::ctor::nil_());
  } else {
    unsigned int m = n - 1;
    return List::list<unsigned int>::ctor::cons_(n,
                                                 countdown_acc(std::move(m)));
  }
}

std::shared_ptr<List::list<unsigned int>>
AccRect::countdown(const unsigned int _x0) {
  return countdown_acc(_x0);
}

unsigned int AccRect::div2_wf(const unsigned int x) {
  if (x <= 0) {
    return 0;
  } else {
    unsigned int n0 = x - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int m = n0 - 1;
      return (div2_wf(m) + 1);
    }
  }
}

unsigned int AccRect::gcd_wf(const unsigned int x, const unsigned int b) {
  if (x <= 0) {
    return std::move(b);
  } else {
    unsigned int a_ = x - 1;
    unsigned int y = Nat::modulo(b, (std::move(a_) + 1));
    return gcd_wf(std::move(y), (std::move(a_) + 1));
  }
}
