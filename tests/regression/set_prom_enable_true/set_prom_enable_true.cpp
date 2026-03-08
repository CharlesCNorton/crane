#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_enable_true.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
SetPromEnableTrue::rom(const std::shared_ptr<SetPromEnableTrue::state> &s) {
  return s->rom;
}

unsigned int SetPromEnableTrue::prom_addr(
    const std::shared_ptr<SetPromEnableTrue::state> &s) {
  return s->prom_addr;
}

unsigned int SetPromEnableTrue::prom_data(
    const std::shared_ptr<SetPromEnableTrue::state> &s) {
  return s->prom_data;
}

bool SetPromEnableTrue::prom_enable(
    const std::shared_ptr<SetPromEnableTrue::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<SetPromEnableTrue::state>
SetPromEnableTrue::set_prom_params(std::shared_ptr<SetPromEnableTrue::state> s,
                                   const unsigned int addr,
                                   const unsigned int data, const bool enable) {
  return std::make_shared<SetPromEnableTrue::state>(state{
      std::move(s)->rom, std::move(addr), std::move(data), std::move(enable)});
}

bool Bool::eqb(const bool b1, const bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}
