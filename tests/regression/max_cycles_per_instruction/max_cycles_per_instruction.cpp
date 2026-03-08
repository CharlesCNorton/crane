#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <max_cycles_per_instruction.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
MaxCyclesPerInstruction::cycles(const MaxCyclesPerInstruction::instr i) {
  return [&](void) {
    switch (i) {
    case instr::NOP: {
      return 8u;
    }
    case instr::ADD: {
      return 8u;
    }
    case instr::WRM: {
      return 8u;
    }
    case instr::FIM: {
      return 16u;
    }
    case instr::JMS: {
      return 24u;
    }
    case instr::JCNTaken: {
      return 16u;
    }
    case instr::JCNNotTaken: {
      return 8u;
    }
    case instr::ISZTaken: {
      return 16u;
    }
    case instr::ISZZero: {
      return 8u;
    }
    }
  }();
}
