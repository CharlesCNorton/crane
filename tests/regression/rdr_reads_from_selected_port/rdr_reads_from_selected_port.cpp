#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rdr_reads_from_selected_port.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int RdrReadsFromSelectedPort::acc(
    const std::shared_ptr<RdrReadsFromSelectedPort::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> RdrReadsFromSelectedPort::rom_ports(
    const std::shared_ptr<RdrReadsFromSelectedPort::state> &s) {
  return s->rom_ports;
}

unsigned int RdrReadsFromSelectedPort::sel_rom(
    const std::shared_ptr<RdrReadsFromSelectedPort::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<RdrReadsFromSelectedPort::state>
RdrReadsFromSelectedPort::execute_rdr(
    std::shared_ptr<RdrReadsFromSelectedPort::state> s) {
  return std::make_shared<RdrReadsFromSelectedPort::state>(
      state{s->rom_ports->nth(s->sel_rom, 0), s->rom_ports, s->sel_rom});
}
