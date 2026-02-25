#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <sigma_compute.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<SigT::sigT<unsigned int, dummy_prop>>
SigmaCompute::nat_with_double(const unsigned int n) {
  return SigT::sigT<unsigned int, dummy_prop>::ctor::existT_((n + n), "dummy");
}

std::shared_ptr<Sig0::sig0<unsigned int>>
SigmaCompute::positive_succ(const unsigned int n) {
  return (std::move(n) + 1);
}

unsigned int SigmaCompute::get_positive(const unsigned int _x0) {
  return positive_succ(_x0);
}

std::shared_ptr<Sig0::sig0<unsigned int>>
SigmaCompute::double_positive(const unsigned int n) {
  std::shared_ptr<Sig0::sig0<unsigned int>> p = positive_succ(n);
  return (p + p);
}

unsigned int SigmaCompute::use_nat_double(const unsigned int n) {
  return nat_with_double(n)->projT1();
}

std::shared_ptr<List::list<unsigned int>>
SigmaCompute::positives_up_to(const unsigned int k) {
  if (k <= 0) {
    return List::list<unsigned int>::ctor::nil_();
  } else {
    unsigned int k_ = k - 1;
    return List::list<unsigned int>::ctor::cons_(positive_succ(k_),
                                                 positives_up_to(k_));
  }
}
