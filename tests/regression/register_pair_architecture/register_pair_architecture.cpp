#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <register_pair_architecture.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool PeanoNat::eqb(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      unsigned int _x = m - 1;
      return false;
    }
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::eqb(n_, m_);
    }
  }
}

bool PeanoNat::leb(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return PeanoNat::leb(n_, m_);
    }
  }
}

bool PeanoNat::ltb(const unsigned int n, const unsigned int m) {
  return PeanoNat::leb((std::move(n) + 1), m);
}

std::pair<unsigned int, unsigned int> PeanoNat::divmod(const unsigned int x,
                                                       const unsigned int y,
                                                       const unsigned int q,
                                                       const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return PeanoNat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return PeanoNat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

unsigned int PeanoNat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return PeanoNat::divmod(x, y_, 0u, y_).first;
  }
}

unsigned int RegisterPairArchitecture::pair_index(const unsigned int r) {
  return PeanoNat::div(r, 2u);
}

bool RegisterPairArchitecture::pair_property(const unsigned int r) {
  unsigned int p = pair_index(r);
  return (PeanoNat::ltb(p, 8u) &&
          (PeanoNat::eqb(r, (2u * p)) || PeanoNat::eqb(r, ((2u * p) + 1u))));
}

std::shared_ptr<List<unsigned int>> ListDef::seq(const unsigned int start,
                                                 const unsigned int len) {
  if (len <= 0) {
    return List<unsigned int>::ctor::nil_();
  } else {
    unsigned int len0 = len - 1;
    return List<unsigned int>::ctor::cons_(start,
                                           ListDef::seq((start + 1), len0));
  }
}
