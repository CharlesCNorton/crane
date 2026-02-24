#include <algorithm>
#include <any>
#include <cassert>
#include <cps.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

bool even(const unsigned int n) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      unsigned int n_ = n0 - 1;
      return even(n_);
    }
  }
}

unsigned int factorial(const unsigned int n) {
  return fact_cps(n, [](unsigned int x) { return x; });
}

unsigned int fibonacci(const unsigned int n) {
  return fib_cps(n, [](unsigned int x) { return x; });
}

unsigned int list_sum(const std::shared_ptr<List::list<unsigned int>> &l) {
  return sum_cps(l, [](unsigned int x) { return x; });
}

unsigned int count_evens(const std::shared_ptr<List::list<unsigned int>> &l) {
  return partition_cps(even, l,
                       [](std::shared_ptr<List::list<unsigned int>> yes,
                          std::shared_ptr<List::list<unsigned int>> _x) {
                         return yes->length();
                       });
}
