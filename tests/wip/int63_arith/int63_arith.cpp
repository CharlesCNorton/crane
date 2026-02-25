#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <int63_arith.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

int64_t Int63Arith::i_abs(const int64_t x) {
  if ((x < 0)) {
    return ((0 - x) & 0x7FFFFFFFFFFFFFFFLL);
  } else {
    return x;
  }
}
