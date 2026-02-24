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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<List::list<A>> nil_uptr() {
        return std::unique_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::unique_ptr<List::list<A>>
      cons_uptr(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::unique_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

struct department;
struct employee;
struct Department {
  struct department {
  public:
    struct mk_department {
      unsigned int _a0;
      std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>> _a1;
    };
    using variant_t = std::variant<mk_department>;

  private:
    variant_t v_;
    explicit department(mk_department _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Department::department> mk_department_(
          unsigned int a0,
          const std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>>
              &a1) {
        return std::shared_ptr<Department::department>(
            new Department::department(mk_department{a0, a1}));
      }
      static std::unique_ptr<Department::department> mk_department_uptr(
          unsigned int a0,
          const std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>>
              &a1) {
        return std::unique_ptr<Department::department>(
            new Department::department(mk_department{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int dept_id() const {
      return std::visit(
          Overloaded{
              [](const typename Department::department::mk_department _args)
                  -> unsigned int {
                unsigned int id = _args._a0;
                return std::move(id);
              }},
          this->v());
    }
    unsigned int dept_total_salary() const {
      return std::visit(
          Overloaded{
              [](const typename Department::department::mk_department _args)
                  -> unsigned int {
                std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>>
                    emps = _args._a1;
                return emp_list_salary(std::move(emps));
              }},
          this->v());
    }
    unsigned int dept_count() const {
      return std::visit(
          Overloaded{
              [](const typename Department::department::mk_department _args)
                  -> unsigned int {
                std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>>
                    emps = _args._a1;
                return emp_list_count(std::move(emps));
              }},
          this->v());
    }
  };
};
struct Employee {
  struct employee {
  public:
    struct mk_employee {
      unsigned int _a0;
      unsigned int _a1;
    };
    using variant_t = std::variant<mk_employee>;

  private:
    variant_t v_;
    explicit employee(mk_employee _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Employee::employee> mk_employee_(unsigned int a0,
                                                              unsigned int a1) {
        return std::shared_ptr<Employee::employee>(
            new Employee::employee(mk_employee{a0, a1}));
      }
      static std::unique_ptr<Employee::employee>
      mk_employee_uptr(unsigned int a0, unsigned int a1) {
        return std::unique_ptr<Employee::employee>(
            new Employee::employee(mk_employee{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int emp_id() const {
      return std::visit(
          Overloaded{[](const typename Employee::employee::mk_employee _args)
                         -> unsigned int {
            unsigned int id = _args._a0;
            return std::move(id);
          }},
          this->v());
    }
    unsigned int emp_salary() const {
      return std::visit(
          Overloaded{[](const typename Employee::employee::mk_employee _args)
                         -> unsigned int {
            unsigned int sal = _args._a1;
            return std::move(sal);
          }},
          this->v());
    }
  };
};

unsigned int emp_list_salary(
    const std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>> &l);

unsigned int emp_list_count(
    const std::shared_ptr<List::list<std::shared_ptr<Employee::employee>>> &l);

const std::shared_ptr<Employee::employee> emp1 = Employee::employee::ctor::mk_employee_((0 + 1), ((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<Employee::employee> emp2 = Employee::employee::ctor::mk_employee_(((0 + 1) + 1), ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<Employee::employee> emp3 = Employee::employee::ctor::mk_employee_((((0 + 1) + 1) + 1), ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

const std::shared_ptr<Department::department> test_dept = Department::department::ctor::mk_department_(((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), List::list<std::shared_ptr<Employee::employee>>::ctor::cons_(emp1, List::list<std::shared_ptr<Employee::employee>>::ctor::cons_(emp2, List::list<std::shared_ptr<Employee::employee>>::ctor::cons_(emp3, List::list<std::shared_ptr<Employee::employee>>::ctor::nil_()))));

const unsigned int test_total_salary = test_dept->dept_total_salary();

const unsigned int test_dept_count = test_dept->dept_count();

const unsigned int test_dept_id = test_dept->dept_id();
