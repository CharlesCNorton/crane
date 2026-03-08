#include <algorithm>
#include <any>
#include <cassert>
#include <encode_clb_bytes_in_range.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::pair<unsigned int, unsigned int>
EncodeClbBytesInRange::encode(const EncodeClbBytesInRange::instruction i) {
  return [&](void) {
    switch (i) {
    case instruction::CLB: {
      return std::make_pair(240u, 0u);
    }
    }
  }();
}

bool EncodeClbBytesInRange::pair_in_range(
    const std::pair<unsigned int, unsigned int> p) {
  unsigned int b1 = p.first;
  unsigned int b2 = p.second;
  return ((b1 < 256u) && (b2 < 256u));
}
