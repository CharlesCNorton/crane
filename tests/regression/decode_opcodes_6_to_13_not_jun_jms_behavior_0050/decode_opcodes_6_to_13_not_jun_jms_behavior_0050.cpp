#include <algorithm>
#include <any>
#include <cassert>
#include <decode_opcodes_6_to_13_not_jun_jms_behavior_0050.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_bank>
DecodeOpcodes6To13NotJunJmsBehavior0050::get_bank(
    const std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::state> &s,
    const unsigned int b) {
  return s->ram_sys->nth(b, empty_bank);
}

std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_chip>
DecodeOpcodes6To13NotJunJmsBehavior0050::get_chip(
    const std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_bank>
        &bk,
    const unsigned int c) {
  return bk->bank_chips->nth(c, empty_chip);
}

std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_reg>
DecodeOpcodes6To13NotJunJmsBehavior0050::get_regRAM(
    const std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_chip>
        &ch,
    const unsigned int r) {
  return ch->chip_regs->nth(r, empty_reg);
}

unsigned int DecodeOpcodes6To13NotJunJmsBehavior0050::get_main(
    const std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_reg> &rg,
    const unsigned int i) {
  return rg->reg_main->nth(i, 0);
}

unsigned int DecodeOpcodes6To13NotJunJmsBehavior0050::ram_read_main(
    const std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::state> &s) {
  std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_bank> bk =
      get_bank(s, s->cur_bank);
  std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_chip> ch =
      get_chip(std::move(bk), s->sel_ram->sel_chip);
  std::shared_ptr<DecodeOpcodes6To13NotJunJmsBehavior0050::ram_reg> rg =
      get_regRAM(std::move(ch), s->sel_ram->sel_reg);
  return get_main(std::move(rg), s->sel_ram->sel_char);
}
