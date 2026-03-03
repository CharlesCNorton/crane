#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <keyword_double_global.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int KeywordDoubleGlobal::double_(const unsigned int n) {
  return (n + n);
}
