#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <src_wrr_rom_port_roundtrip.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> SrcWrrRomPortRoundtrip::regs(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s) {
  return s->regs;
}

unsigned int SrcWrrRomPortRoundtrip::acc(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> SrcWrrRomPortRoundtrip::rom_ports(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s) {
  return s->rom_ports;
}

unsigned int SrcWrrRomPortRoundtrip::sel_rom(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s) {
  return s->sel_rom;
}

unsigned int SrcWrrRomPortRoundtrip::get_reg(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int SrcWrrRomPortRoundtrip::get_reg_pair(
    const std::shared_ptr<SrcWrrRomPortRoundtrip::state> &s,
    const unsigned int r) {
  unsigned int base =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  return ((get_reg(s, base) *
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)) +
          get_reg(s, (base + (0 + 1))));
}

std::shared_ptr<SrcWrrRomPortRoundtrip::state>
SrcWrrRomPortRoundtrip::execute_src(
    std::shared_ptr<SrcWrrRomPortRoundtrip::state> s, const unsigned int r) {
  return std::make_shared<SrcWrrRomPortRoundtrip::state>(state{
      s->regs, s->acc, s->rom_ports,
      Nat::div(
          get_reg_pair(s, std::move(r)),
          ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1))});
}

std::shared_ptr<SrcWrrRomPortRoundtrip::state>
SrcWrrRomPortRoundtrip::execute_wrr(
    std::shared_ptr<SrcWrrRomPortRoundtrip::state> s) {
  return std::make_shared<SrcWrrRomPortRoundtrip::state>(state{
      s->regs, s->acc,
      update_nth<unsigned int>(s->sel_rom, s->acc, s->rom_ports), s->sel_rom});
}

std::pair<unsigned int, unsigned int> Nat::divmod(const unsigned int x,
                                                  const unsigned int y,
                                                  const unsigned int q,
                                                  const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

unsigned int Nat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0, y_).first;
  }
}
