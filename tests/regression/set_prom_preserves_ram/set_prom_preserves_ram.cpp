#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_preserves_ram.h>
#include <stdexcept>
#include <string>
#include <variant>

bool SetPromPreservesRam::nat_list_eqb(
    const std::shared_ptr<List<unsigned int>> &xs,
    const std::shared_ptr<List<unsigned int>> &ys) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::nil _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args) -> bool {
                      return true;
                    },
                    [](const typename List<unsigned int>::cons _args) -> bool {
                      return false;
                    }},
                ys->v());
          },
          [&](const typename List<unsigned int>::cons _args) -> bool {
            unsigned int x = _args._a0;
            std::shared_ptr<List<unsigned int>> xs_ = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args) -> bool {
                      return false;
                    },
                    [&](const typename List<unsigned int>::cons _args) -> bool {
                      unsigned int y = _args._a0;
                      std::shared_ptr<List<unsigned int>> ys_ = _args._a1;
                      return ((std::move(x) == std::move(y)) &&
                              nat_list_eqb(std::move(xs_), std::move(ys_)));
                    }},
                ys->v());
          }},
      xs->v());
}

std::shared_ptr<List<unsigned int>> SetPromPreservesRam::regs(
    const std::shared_ptr<SetPromPreservesRam::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> SetPromPreservesRam::ram_sys(
    const std::shared_ptr<SetPromPreservesRam::state> &s) {
  return s->ram_sys;
}

unsigned int SetPromPreservesRam::prom_addr(
    const std::shared_ptr<SetPromPreservesRam::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromPreservesRam::prom_data(
    const std::shared_ptr<SetPromPreservesRam::state> &s) {
  return s->prom_data;
}

bool SetPromPreservesRam::prom_enable(
    const std::shared_ptr<SetPromPreservesRam::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromPreservesRam::state>
SetPromPreservesRam::set_prom_params(
    std::shared_ptr<SetPromPreservesRam::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<SetPromPreservesRam::state>(
      state{s->regs, s->ram_sys, std::move(addr), std::move(data),
            std::move(enable)});
}
