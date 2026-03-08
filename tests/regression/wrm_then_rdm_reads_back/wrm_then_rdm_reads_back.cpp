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
#include <wrm_then_rdm_reads_back.h>

std::shared_ptr<List<unsigned int>> WrmThenRdmReadsBack::regs(
    const std::shared_ptr<WrmThenRdmReadsBack::state> &s) {
  return s->regs;
}

unsigned int
WrmThenRdmReadsBack::acc(const std::shared_ptr<WrmThenRdmReadsBack::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>>
WrmThenRdmReadsBack::ram(const std::shared_ptr<WrmThenRdmReadsBack::state> &s) {
  return s->ram;
}

unsigned int WrmThenRdmReadsBack::sel_char(
    const std::shared_ptr<WrmThenRdmReadsBack::state> &s) {
  return s->sel_char;
}

unsigned int WrmThenRdmReadsBack::get_reg(
    const std::shared_ptr<WrmThenRdmReadsBack::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

unsigned int WrmThenRdmReadsBack::get_reg_pair(
    const std::shared_ptr<WrmThenRdmReadsBack::state> &s,
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

std::shared_ptr<WrmThenRdmReadsBack::state>
WrmThenRdmReadsBack::execute_src(std::shared_ptr<WrmThenRdmReadsBack::state> s,
                                 const unsigned int r) {
  return std::make_shared<WrmThenRdmReadsBack::state>(state{
      s->regs, s->acc, s->ram,
      (get_reg_pair(s, std::move(r)) %
       ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1) +
        1))});
}

std::shared_ptr<WrmThenRdmReadsBack::state> WrmThenRdmReadsBack::execute_wrm(
    std::shared_ptr<WrmThenRdmReadsBack::state> s) {
  return std::make_shared<WrmThenRdmReadsBack::state>(state{
      s->regs, s->acc, update_nth<unsigned int>(s->sel_char, s->acc, s->ram),
      s->sel_char});
}

std::shared_ptr<WrmThenRdmReadsBack::state> WrmThenRdmReadsBack::execute_rdm(
    std::shared_ptr<WrmThenRdmReadsBack::state> s) {
  return std::make_shared<WrmThenRdmReadsBack::state>(
      state{s->regs, s->ram->nth(s->sel_char, 0), s->ram, s->sel_char});
}
