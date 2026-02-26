#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rec_record.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int RecRecord::rn_value(const std::shared_ptr<RecRecord::RNode> &r) {
  return r->rn_value;
}

std::optional<std::shared_ptr<RecRecord::RNode>>
RecRecord::rn_next(const std::shared_ptr<RecRecord::RNode> &r) {
  return r->rn_next;
}

unsigned int
RecRecord::emp_name(const std::shared_ptr<RecRecord::Employee> &e) {
  return e->emp_name;
}

unsigned int
RecRecord::emp_dept(const std::shared_ptr<RecRecord::Employee> &e) {
  return e->emp_dept;
}

unsigned int
RecRecord::dept_id(const std::shared_ptr<RecRecord::Department> &d) {
  return d->dept_id;
}

std::shared_ptr<RecRecord::Employee>
RecRecord::dept_head(const std::shared_ptr<RecRecord::Department> &d) {
  return d->dept_head;
}

unsigned int
RecRecord::dept_size(const std::shared_ptr<RecRecord::Department> &d) {
  return d->dept_size;
}

unsigned int
RecRecord::rlist_sum(const std::shared_ptr<RecRecord::rlist<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename RecRecord::rlist<unsigned int>::rnil _args)
                     -> unsigned int { return 0; },
                 [](const typename RecRecord::rlist<unsigned int>::rcons _args)
                     -> unsigned int {
                   unsigned int x = _args._a0;
                   std::shared_ptr<RecRecord::rlist<unsigned int>> rest =
                       _args._a1;
                   return (std::move(x) + rlist_sum(std::move(rest)));
                 }},
      l->v());
}

unsigned int
RecRecord::rnode_depth(const std::shared_ptr<RecRecord::RNode> &r) {
  if (r->rn_next.has_value()) {
    std::shared_ptr<RecRecord::RNode> next = *r->rn_next;
    return (rnode_depth(next) + 1);
  } else {
    return (0 + 1);
  }
}
