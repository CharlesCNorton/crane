#include <algorithm>
#include <any>
#include <cassert>
#include <decode_wf_opcode_14_behavior_0084.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_bank>
DecodeWfOpcode14Behavior0084::get_bank(
    const std::shared_ptr<DecodeWfOpcode14Behavior0084::state> &s,
    const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}

std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_chip>
DecodeWfOpcode14Behavior0084::get_chip(
    const std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_bank> &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(c, empty_chip);
}

std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_reg>
DecodeWfOpcode14Behavior0084::get_regRAM(
    const std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_chip> &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, empty_reg);
}

unsigned int DecodeWfOpcode14Behavior0084::get_main(
    const std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_reg> &rg,
    const unsigned int i) {
  return rg->reg_main->nth(i, 0);
}

unsigned int DecodeWfOpcode14Behavior0084::ram_read_main(
    const std::shared_ptr<DecodeWfOpcode14Behavior0084::state> &s) {
  std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_bank> bk =
      get_bank(s, s->cur_bank);
  std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_chip> ch =
      get_chip(std::move(bk), s->sel_ram->sel_chip);
  std::shared_ptr<DecodeWfOpcode14Behavior0084::ram_reg> rg =
      get_regRAM(std::move(ch), s->sel_ram->sel_reg);
  return get_main(std::move(rg), s->sel_ram->sel_char);
}
