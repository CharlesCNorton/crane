#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <wrr_rdr_roundtrip.h>

unsigned int
WrrRdrRoundtrip::acc(const std::shared_ptr<WrrRdrRoundtrip::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>>
WrrRdrRoundtrip::rom_ports(const std::shared_ptr<WrrRdrRoundtrip::state> &s) {
  return s->rom_ports;
}

unsigned int
WrrRdrRoundtrip::sel_rom(const std::shared_ptr<WrrRdrRoundtrip::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<WrrRdrRoundtrip::state>
WrrRdrRoundtrip::execute_wrr(std::shared_ptr<WrrRdrRoundtrip::state> s) {
  return std::make_shared<WrrRdrRoundtrip::state>(
      state{s->acc, update_nth<unsigned int>(s->sel_rom, s->acc, s->rom_ports),
            s->sel_rom});
}

std::shared_ptr<WrrRdrRoundtrip::state>
WrrRdrRoundtrip::execute_rdr(std::shared_ptr<WrrRdrRoundtrip::state> s) {
  return std::make_shared<WrrRdrRoundtrip::state>(
      state{s->rom_ports->nth(s->sel_rom, 0), s->rom_ports, s->sel_rom});
}
