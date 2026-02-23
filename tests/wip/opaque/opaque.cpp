#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <opaque.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int safe_pred(const unsigned int n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = n - 1;
    return n0;
  }
}

unsigned int pred_of_succ(const unsigned int n) {
  return safe_pred((std::move(n) + 1));
}

bool nat_eq_dec(const unsigned int n, const unsigned int x) {
  if (n <= 0) {
    if (x <= 0) {
      return true;
    } else {
      unsigned int _x = x - 1;
      return false;
    }
  } else {
    unsigned int n0 = n - 1;
    if (x <= 0) {
      return false;
    } else {
      unsigned int n1 = x - 1;
      if (nat_eq_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool are_equal(const unsigned int n, const unsigned int m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}
