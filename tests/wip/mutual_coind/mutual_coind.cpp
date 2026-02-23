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

std::shared_ptr<StreamA::streamA<unsigned int>> countA(const unsigned int n) {
  return StreamA::streamA<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<StreamA::streamA<unsigned int>> {
        return StreamA::streamA<unsigned int>::ctor::consA_(n, countB((n + 1)));
      });
}
std::shared_ptr<StreamB::streamB<unsigned int>> countB(const unsigned int n) {
  return StreamB::streamB<unsigned int>::ctor::lazy_(
      [=](void) -> std::shared_ptr<StreamB::streamB<unsigned int>> {
        return StreamB::streamB<unsigned int>::ctor::consB_(n, countA((n + 1)));
      });
}
