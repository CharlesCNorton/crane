#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <mutual_record.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int emp_list_salary(
    const std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List::list<std::shared_ptr<Employee::employee>>::nil
                 _args) -> unsigned int { return 0; },
          [](const typename List::list<std::shared_ptr<Employee::employee>>::
                 cons _args) -> unsigned int {
            std::shared_ptr<Employee::employee> e = _args._a0;
            std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>>
                rest = _args._a1;
            return (std::move(e)->emp_salary() +
                    emp_list_salary(std::move(rest)));
          }},
      l->v());
}

unsigned int emp_list_count(
    const std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List::list<std::shared_ptr<Employee::employee>>::nil
                 _args) -> unsigned int { return 0; },
          [](const typename List::list<std::shared_ptr<Employee::employee>>::
                 cons _args) -> unsigned int {
            std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>>
                rest = _args._a1;
            return ((0 + 1) + emp_list_count(std::move(rest)));
          }},
      l->v());
}
