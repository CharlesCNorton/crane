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

int64_t Int63Arith::test_add(const int64_t _x0, const int64_t _x1) {
  return ((_x0 + _x1) & 0x7FFFFFFFFFFFFFFFLL);
}

int64_t Int63Arith::test_sub(const int64_t _x0, const int64_t _x1) {
  return ((_x0 - _x1) & 0x7FFFFFFFFFFFFFFFLL);
}

int64_t Int63Arith::test_mul(const int64_t _x0, const int64_t _x1) {
  return ((_x0 * _x1) & 0x7FFFFFFFFFFFFFFFLL);
}

int64_t Int63Arith::test_div(const int64_t _x0, const int64_t _x1) {
  return (_x1 == 0 ? 0 : _x0 / _x1);
}

int64_t Int63Arith::test_mod(const int64_t _x0, const int64_t _x1) {
  return (_x1 == 0 ? 0 : _x0 % _x1);
}

int64_t Int63Arith::test_land(const int64_t _x0, const int64_t _x1) {
  return (_x0 & _x1);
}

int64_t Int63Arith::test_lor(const int64_t _x0, const int64_t _x1) {
  return (_x0 | _x1);
}

int64_t Int63Arith::test_lxor(const int64_t _x0, const int64_t _x1) {
  return (_x0 ^ _x1);
}

int64_t Int63Arith::test_lsl(const int64_t _x0, const int64_t _x1) {
  return (_x1 >= 63 ? 0 : ((_x0 << _x1) & 0x7FFFFFFFFFFFFFFFLL));
}

int64_t Int63Arith::test_lsr(const int64_t _x0, const int64_t _x1) {
  return (_x1 >= 63 ? 0 : (_x0 >> _x1));
}

bool Int63Arith::test_eqb(const int64_t _x0, const int64_t _x1) {
  return (_x0 == _x1);
}

bool Int63Arith::test_ltb(const int64_t _x0, const int64_t _x1) {
  return (_x0 < _x1);
}

bool Int63Arith::test_leb(const int64_t _x0, const int64_t _x1) {
  return (_x0 <= _x1);
}
