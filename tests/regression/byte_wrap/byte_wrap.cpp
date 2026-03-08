#include <algorithm>
#include <any>
#include <byte_wrap.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int ByteWrap::byte_of_nat(const unsigned int n) { return (n % 256u); }
