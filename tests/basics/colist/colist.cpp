#include <algorithm>
#include <any>
#include <cassert>
#include <colist.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Colist::colist<std::shared_ptr<Nat>>>
Colist::nats(std::shared_ptr<Nat> n) {
  return colist<std::shared_ptr<Nat>>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Colist::colist<std::shared_ptr<Nat>>> {
        return colist<std::shared_ptr<Nat>>::ctor::cocons_(
            n, nats(Nat::ctor::S_(n)));
      });
}
