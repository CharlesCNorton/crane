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
      return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
    }
    case instr::ADD: {
      return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
    }
    case instr::WRM: {
      return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
    }
    case instr::FIM: {
      return (
          (((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1);
    }
    case instr::JMS: {
      return ((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1) +
                1) +
               1) +
              1);
    }
    case instr::JCNTaken: {
      return (
          (((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1);
    }
    case instr::JCNNotTaken: {
      return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
    }
    case instr::ISZTaken: {
      return (
          (((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1);
    }
    case instr::ISZZero: {
      return ((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1);
    }
    }
  }();
}
