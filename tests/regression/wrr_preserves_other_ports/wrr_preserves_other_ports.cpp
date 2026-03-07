#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <wrr_preserves_other_ports.h>

unsigned int WrrPreservesOtherPorts::acc(
    const std::shared_ptr<WrrPreservesOtherPorts::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> WrrPreservesOtherPorts::rom_ports(
    const std::shared_ptr<WrrPreservesOtherPorts::state> &s) {
  return s->rom_ports;
}

unsigned int WrrPreservesOtherPorts::sel_rom(
    const std::shared_ptr<WrrPreservesOtherPorts::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<WrrPreservesOtherPorts::state>
WrrPreservesOtherPorts::execute_wrr(
    std::shared_ptr<WrrPreservesOtherPorts::state> s) {
  return std::make_shared<WrrPreservesOtherPorts::state>(state{
      s->acc,
      update_nth<unsigned int>(
          s->sel_rom,
          (s->acc %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          s->rom_ports),
      s->sel_rom});
}
