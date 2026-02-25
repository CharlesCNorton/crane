#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <int63_arith.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

int Int63Arith::i_abs(const int x) {
  if (x < 0) {
    return 0 - x;
  } else {
    return x;
  }
}
