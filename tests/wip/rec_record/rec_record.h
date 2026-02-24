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

struct Rlist {
  template <typename A> struct rlist {
  public:
    struct rnil {};
    struct rcons {
      A _a0;
      std::shared_ptr<Rlist::rlist<A>> _a1;
    };
    using variant_t = std::variant<rnil, rcons>;

  private:
    variant_t v_;
    explicit rlist(rnil _v) : v_(std::move(_v)) {}
    explicit rlist(rcons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Rlist::rlist<A>> rnil_() {
        return std::shared_ptr<Rlist::rlist<A>>(new Rlist::rlist<A>(rnil{}));
      }
      static std::shared_ptr<Rlist::rlist<A>>
      rcons_(A a0, const std::shared_ptr<Rlist::rlist<A>> &a1) {
        return std::shared_ptr<Rlist::rlist<A>>(
            new Rlist::rlist<A>(rcons{a0, a1}));
      }
      static std::unique_ptr<Rlist::rlist<A>> rnil_uptr() {
        return std::unique_ptr<Rlist::rlist<A>>(new Rlist::rlist<A>(rnil{}));
      }
      static std::unique_ptr<Rlist::rlist<A>>
      rcons_uptr(A a0, const std::shared_ptr<Rlist::rlist<A>> &a1) {
        return std::unique_ptr<Rlist::rlist<A>>(
            new Rlist::rlist<A>(rcons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int rlist_length() const {
      return std::visit(
          Overloaded{
              [](const typename Rlist::rlist<A>::rnil _args) -> unsigned int {
                return 0;
              },
              [](const typename Rlist::rlist<A>::rcons _args) -> unsigned int {
                std::shared_ptr<Rlist::rlist<A>> rest = _args._a1;
                return (std::move(rest)->rlist_length() + 1);
              }},
          this->v());
    }
    unsigned int rlist_sum() const {
      return std::visit(
          Overloaded{[](const typename Rlist::rlist<unsigned int>::rnil _args)
                         -> unsigned int { return 0; },
                     [](const typename Rlist::rlist<unsigned int>::rcons _args)
                         -> unsigned int {
                       unsigned int x = _args._a0;
                       std::shared_ptr<Rlist::rlist<unsigned int>> rest =
                           _args._a1;
                       return (std::move(x) + std::move(rest)->rlist_sum());
                     }},
          this->v());
    }
  };
};

struct RNode {
  unsigned int rn_value;
  std::optional<std::shared_ptr<RNode>> rn_next;
};

struct Employee {
  unsigned int emp_name;
  unsigned int emp_dept;
};

struct Department {
  unsigned int dept_id;
  std::shared_ptr<Employee> dept_head;
  unsigned int dept_size;
};

const std::shared_ptr<Rlist::rlist<unsigned int>> test_rlist =
    Rlist::rlist<unsigned int>::ctor::rcons_(
        (0 + 1),
        Rlist::rlist<unsigned int>::ctor::rcons_(
            ((0 + 1) + 1), Rlist::rlist<unsigned int>::ctor::rcons_(
                               (((0 + 1) + 1) + 1),
                               Rlist::rlist<unsigned int>::ctor::rnil_())));

const unsigned int test_rlist_len = test_rlist->rlist_length();

const unsigned int test_rlist_sum = test_rlist->rlist_sum();

const std::shared_ptr<RNode> test_rnode = std::make_shared<RNode>(RNode{
    (0 + 1),
    std::make_optional<std::shared_ptr<RNode>>(std::make_shared<RNode>(RNode{
        ((0 + 1) + 1),
        std::make_optional<std::shared_ptr<RNode>>(std::make_shared<RNode>(
            RNode{(((0 + 1) + 1) + 1), std::nullopt}))}))});

const unsigned int test_rnode_depth = test_rnode->rnode_depth();

const std::shared_ptr<Employee> test_emp = std::make_shared<Employee>(Employee{
    ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
          1) +
         1) +
        1) +
       1) +
      1) +
     1),
    (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)});

const std::shared_ptr<Department> test_dept = std::make_shared<Department>(Department{(((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1), test_emp, ((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)});

const unsigned int test_dept_head_name = test_dept->dept_head->emp_name;
