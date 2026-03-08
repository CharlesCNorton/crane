#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_write_main_preserves_other_bank.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> RamWriteMainPreservesOtherBank::ram_sys(
    const std::shared_ptr<RamWriteMainPreservesOtherBank::state> &s) {
  return s->ram_sys;
}

unsigned int RamWriteMainPreservesOtherBank::cur_bank(
    const std::shared_ptr<RamWriteMainPreservesOtherBank::state> &s) {
  return s->cur_bank;
}

std::shared_ptr<List<unsigned int>>
RamWriteMainPreservesOtherBank::ram_write_main_sys(
    const std::shared_ptr<RamWriteMainPreservesOtherBank::state> &s,
    const unsigned int v) {
  return update_nth<unsigned int>(s->cur_bank, v, s->ram_sys);
}

std::shared_ptr<RamWriteMainPreservesOtherBank::state>
RamWriteMainPreservesOtherBank::execute_write(
    std::shared_ptr<RamWriteMainPreservesOtherBank::state> s,
    const unsigned int v) {
  return std::make_shared<RamWriteMainPreservesOtherBank::state>(
      state{ram_write_main_sys(s, std::move(v)), s->cur_bank});
}
