#include <algorithm>
#include <any>
#include <axiom_types.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

AxiomTypes::MysteryType
AxiomTypes::mystery_function(const AxiomTypes::MysteryType _x0) {
  throw std::logic_error("unrealized axiom: "
                         "CraneTestsRegression.axiom_types.AxiomTypes."
                         "AxiomTypes.mystery_function");
}

AxiomTypes::MysteryType AxiomTypes::extract_axiom_field(
    const std::shared_ptr<AxiomTypes::AxiomRecord> &r) {
  return r->axiom_field;
}

AxiomTypes::MysteryType
AxiomTypes::axiom_identity(const AxiomTypes::MysteryType x) {
  return x;
}
