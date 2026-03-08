#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <load_program_step_preserves_wf_simple.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<LoadProgramStepPreservesWfSimple::state>
LoadProgramStepPreservesWfSimple::set_prom_params(
    std::shared_ptr<LoadProgramStepPreservesWfSimple::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<LoadProgramStepPreservesWfSimple::state>(
      state{s->regs_len, s->rom, s->pc, s->stack_len, std::move(addr),
            std::move(data), std::move(enable)});
}

std::shared_ptr<LoadProgramStepPreservesWfSimple::state>
LoadProgramStepPreservesWfSimple::execute_wpm(
    std::shared_ptr<LoadProgramStepPreservesWfSimple::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<LoadProgramStepPreservesWfSimple::state>(
      state{s->regs_len, std::move(new_rom), s->pc, s->stack_len, s->prom_addr,
            s->prom_data, s->prom_enable});
}
