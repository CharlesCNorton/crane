#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nibble_wrap.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int NibbleWrap::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}
