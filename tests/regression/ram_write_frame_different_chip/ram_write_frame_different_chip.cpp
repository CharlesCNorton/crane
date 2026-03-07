#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_write_frame_different_chip.h>
#include <stdexcept>
#include <string>
#include <variant>

RamWriteFrameDifferentChip::reg RamWriteFrameDifferentChip::upd_main_in_reg(
    const std::shared_ptr<List<unsigned int>> &rg, const unsigned int i,
    const unsigned int v) {
  return update_nth<unsigned int>(i, v, rg);
}

RamWriteFrameDifferentChip::chip RamWriteFrameDifferentChip::upd_reg_in_chip(
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch,
    const unsigned int r, const std::shared_ptr<List<unsigned int>> &rg) {
  return update_nth<RamWriteFrameDifferentChip::reg>(r, rg, ch);
}

RamWriteFrameDifferentChip::bank RamWriteFrameDifferentChip::upd_chip_in_bank(
    const std::shared_ptr<
        List<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>> &bk,
    const unsigned int c,
    const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch) {
  return update_nth<RamWriteFrameDifferentChip::chip>(c, ch, bk);
}
