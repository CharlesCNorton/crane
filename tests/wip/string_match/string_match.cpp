#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <stdexcept>
#include <string>
#include <string_match.h>
#include <utility>
#include <variant>

bool StringMatch::is_empty(const std::string s) {
  return (s.length() == int64_t(0));
}
