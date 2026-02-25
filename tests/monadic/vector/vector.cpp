#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector.h>
#include <vector>

int64_t vectest::test1(const int64_t _x) {
  std::vector<int64_t> v = {};
  v.push_back(3);
  v.push_back(2);
  v.push_back(7);
  int64_t x = v.size();
  v.pop_back();
  int64_t y = v.size();
  return ((x - y) & 0x7FFFFFFFFFFFFFFFLL);
}

std::vector<int64_t> vectest::test2(const int64_t _x) {
  std::vector<int64_t> v = {};
  v.push_back(12);
  v.push_back(23);
  v.pop_back();
  v.push_back(3);
  int64_t x = v.size();
  v.push_back(x);
  int64_t y = v.at(2);
  v.push_back(98);
  v.push_back(y);
  return v;
}
