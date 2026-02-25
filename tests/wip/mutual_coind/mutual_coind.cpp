#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mutual_coind.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<MutualCoind::streamA<unsigned int>>
MutualCoind::countA(const unsigned int n) {
  return streamA<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<MutualCoind::streamA<unsigned int>> {
        return streamA<unsigned int>::ctor::consA_(n, countB((n + 1)));
      });
}
std::shared_ptr<MutualCoind::streamB<unsigned int>>
MutualCoind::countB(const unsigned int n) {
  return streamB<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<MutualCoind::streamB<unsigned int>> {
        return streamB<unsigned int>::ctor::consB_(n, countA((n + 1)));
      });
}
