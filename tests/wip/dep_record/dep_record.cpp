#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <dep_record.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

DepRecord::carrier DepRecord::op(const std::shared_ptr<DepRecord::magma> &m,
                                 const DepRecord::carrier _x0,
                                 const DepRecord::carrier _x1) {
  return m(_x0, _x1);
}

DepRecord::m_carrier
DepRecord::m_op(const std::shared_ptr<DepRecord::Monoid> &m,
                const DepRecord::m_carrier _x0,
                const DepRecord::m_carrier _x1) {
  return m->m_op(_x0, _x1);
}

DepRecord::m_carrier
DepRecord::m_id(const std::shared_ptr<DepRecord::Monoid> &m) {
  return m->m_id;
}

DepRecord::m_carrier
DepRecord::mfold(const std::shared_ptr<DepRecord::Monoid> &m,
                 const std::shared_ptr<List::list<std::any>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<std::any>::nil _args) -> std::any {
            return m->m_id;
          },
          [&](const typename List::list<std::any>::cons _args) -> std::any {
            std::any x = _args._a0;
            std::shared_ptr<List::list<std::any>> rest = _args._a1;
            return m->m_op(x, mfold(m, rest));
          }},
      l->v());
}

DepRecord::tag DepRecord::the_tag(const std::shared_ptr<DepRecord::Tagged> &t) {
  return t->the_tag;
}

DepRecord::tag_type
DepRecord::the_value(const std::shared_ptr<DepRecord::Tagged> &t) {
  return t->the_value;
}
