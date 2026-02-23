#include <algorithm>
#include <any>
#include <cassert>
#include <equations.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool Nat::leb(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n_ = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int m_ = m - 1;
      return leb(n_, m_);
    }
  }
}

bool Nat::ltb(const unsigned int n, const unsigned int m) {
  return leb((std::move(n) + 1), m);
}

bool Nat::even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      unsigned int n_ = n0 - 1;
      return even(n_);
    }
  }
}

unsigned int Nat::div2(const unsigned int n) {
  if (n <= 0) {
    return 0;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n_ = n0 - 1;
      return (div2(n_) + 1);
    }
  }
}

unsigned int collatz_steps(const unsigned int _x0) {
  return [](const T1 _x0) {
    return FixWf<unsigned int>(collatz_steps_functional, _x0);
  }(_x0);
}

unsigned int gcd(const std::pair<unsigned int, unsigned int> _x0) {
  return [](const T1 _x0) {
    return FixWf<std::pair<unsigned int, unsigned int>>(gcd_functional, _x0);
  }(_x0);
}
