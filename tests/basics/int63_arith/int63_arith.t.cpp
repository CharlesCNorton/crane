// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <int63_arith.h>

#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);

int main() {

  constexpr int64_t mask63 = 0x7FFFFFFFFFFFFFFFLL;

  // ---- Basic arithmetic ----
  ASSERT(Int63Arith::test_add(42, 58) == 100);
  ASSERT(Int63Arith::test_sub(100, 42) == 58);
  ASSERT(Int63Arith::test_mul(7, 6) == 42);
  ASSERT(Int63Arith::test_div(100, 7) == 14);
  ASSERT(Int63Arith::test_mod(100, 7) == 2);

  // ---- Division/modulo by zero ----
  ASSERT(Int63Arith::test_div(42, 0) == 0);
  ASSERT(Int63Arith::test_mod(42, 0) == 0);

  // ---- Bitwise ----
  ASSERT(Int63Arith::test_land(0xFF, 0x0F) == 0x0F);
  ASSERT(Int63Arith::test_lor(0xF0, 0x0F) == 0xFF);
  ASSERT(Int63Arith::test_lxor(0xFF, 0x0F) == 0xF0);

  // ---- Shifts ----
  ASSERT(Int63Arith::test_lsl(1, 10) == 1024);
  ASSERT(Int63Arith::test_lsr(1024, 5) == 32);
  ASSERT(Int63Arith::test_lsl(1, 62) == INT64_C(4611686018427387904));
  ASSERT(Int63Arith::test_lsr(INT64_C(4611686018427387904), 62) == 1);

  // ---- Shift edge cases ----
  ASSERT(Int63Arith::test_lsl(1, 63) == 0);     // shifted past 63-bit range
  ASSERT(Int63Arith::test_lsl(1, 100) == 0);    // large shift
  ASSERT(Int63Arith::test_lsr(mask63, 63) == 0); // shifted past range
  ASSERT(Int63Arith::test_lsr(mask63, 62) == 1); // only top bit survives

  // ---- Comparison ----
  ASSERT(Int63Arith::test_eqb(42, 42) == true);
  ASSERT(Int63Arith::test_eqb(42, 43) == false);
  ASSERT(Int63Arith::test_ltb(41, 42) == true);
  ASSERT(Int63Arith::test_ltb(42, 42) == false);
  ASSERT(Int63Arith::test_leb(42, 42) == true);
  ASSERT(Int63Arith::test_leb(43, 42) == false);

  // ---- Overflow / wrapping ----
  ASSERT(Int63Arith::test_add(mask63, 1) == 0);         // max + 1 wraps to 0
  ASSERT(Int63Arith::test_sub(0, 1) == mask63);          // 0 - 1 wraps to max
  ASSERT(Int63Arith::test_mul(mask63, 2) == (mask63 - 1)); // max * 2 = 2^64-2, masked = 2^63-2

  // ---- Identity checks ----
  ASSERT(Int63Arith::test_add(0, 0) == 0);
  ASSERT(Int63Arith::test_mul(1, mask63) == mask63);
  ASSERT(Int63Arith::test_div(mask63, 1) == mask63);
  ASSERT(Int63Arith::test_mod(mask63, mask63) == 0);
  ASSERT(Int63Arith::test_land(mask63, mask63) == mask63);
  ASSERT(Int63Arith::test_lor(0, 0) == 0);
  ASSERT(Int63Arith::test_lxor(mask63, mask63) == 0);

  return testStatus;
}
