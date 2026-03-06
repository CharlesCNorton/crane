#include <algorithm>
#include <any>
#include <cassert>
#include <decode_instr_wf_jun_jms_behavior_0052.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int DecodeInstrWfJunJmsBehavior0052::fetch_byte(
    const std::shared_ptr<DecodeInstrWfJunJmsBehavior0052::state> &s,
    const unsigned int addr) {
  return s->rom->nth(addr, 0);
}
