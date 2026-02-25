#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prim_float_test.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

double PrimFloatTest::test_add(const double _x0, const double _x1) {
  return (_x0 + _x1);
}

double PrimFloatTest::test_sub(const double _x0, const double _x1) {
  return (_x0 - _x1);
}

double PrimFloatTest::test_mul(const double _x0, const double _x1) {
  return (_x0 * _x1);
}

double PrimFloatTest::test_div(const double _x0, const double _x1) {
  return (_x0 / _x1);
}

double PrimFloatTest::test_opp(const double _x0) { return (-_x0); }

double PrimFloatTest::test_abs(const double _x0) { return std::abs(_x0); }

double PrimFloatTest::test_sqrt(const double _x0) { return std::sqrt(_x0); }

bool PrimFloatTest::test_eqb(const double _x0, const double _x1) {
  return (_x0 == _x1);
}

bool PrimFloatTest::test_ltb(const double _x0, const double _x1) {
  return (_x0 < _x1);
}

bool PrimFloatTest::test_leb(const double _x0, const double _x1) {
  return (_x0 <= _x1);
}

double PrimFloatTest::test_of_uint63(const int64_t _x0) {
  return static_cast<double>(_x0);
}
