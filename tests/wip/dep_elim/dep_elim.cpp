#include <algorithm>
#include <any>
#include <cassert>
#include <dep_elim.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int fin_to_nat(const unsigned int _x,
                        const std::shared_ptr<Fin::fin> &f) {
  return std::visit(
      Overloaded{
          [](const typename Fin::fin::FZ _args) -> unsigned int { return 0; },
          [](const typename Fin::fin::FS _args) -> unsigned int {
            unsigned int n0 = _args._a0;
            std::shared_ptr<Fin::fin> f_ = _args._a1;
            return (fin_to_nat(std::move(n0), std::move(f_)) + 1);
          }},
      f->v());
}
