#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <regexp.h>
#include <string>
#include <utility>
#include <variant>

namespace list {};

namespace Matcher {
bool char_eq(const int x, const int y) {
  bool b = x == y;
  if (b) {
    return true;
  } else {
    return false;
  }
}

namespace regexp {
std::shared_ptr<regexp> Any::make() { return std::make_shared<regexp>(Any{}); }
std::shared_ptr<regexp> Char::make(int _a0) {
  return std::make_shared<regexp>(Char{_a0});
}
std::shared_ptr<regexp> Eps::make() { return std::make_shared<regexp>(Eps{}); }
std::shared_ptr<regexp> Cat::make(std::shared_ptr<regexp> _a0,
                                  std::shared_ptr<regexp> _a1) {
  return std::make_shared<regexp>(Cat{_a0, _a1});
}
std::shared_ptr<regexp> Alt::make(std::shared_ptr<regexp> _a0,
                                  std::shared_ptr<regexp> _a1) {
  return std::make_shared<regexp>(Alt{_a0, _a1});
}
std::shared_ptr<regexp> Zero::make() {
  return std::make_shared<regexp>(Zero{});
}
std::shared_ptr<regexp> Star::make(std::shared_ptr<regexp> _a0) {
  return std::make_shared<regexp>(Star{_a0});
}
}; // namespace regexp

bool regexp_eq(const std::shared_ptr<regexp::regexp> r,
               const std::shared_ptr<regexp::regexp> x) {
  return std::visit(
      Overloaded{
          [&](const regexp::Any _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return true; },
                    [&](const regexp::Char _args) -> bool { return false; },
                    [&](const regexp::Eps _args) -> bool { return false; },
                    [&](const regexp::Cat _args) -> bool { return false; },
                    [&](const regexp::Alt _args) -> bool { return false; },
                    [&](const regexp::Zero _args) -> bool { return false; },
                    [&](const regexp::Star _args) -> bool { return false; }},
                *x);
          },
          [&](const regexp::Char _args) -> T1 {
            int c = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return false; },
                    [&](const regexp::Char _args) -> bool {
                      int c0 = _args._a0;
                      if (char_eq(c, c0)) {
                        return true;
                      } else {
                        return false;
                      }
                    },
                    [&](const regexp::Eps _args) -> bool { return false; },
                    [&](const regexp::Cat _args) -> bool { return false; },
                    [&](const regexp::Alt _args) -> bool { return false; },
                    [&](const regexp::Zero _args) -> bool { return false; },
                    [&](const regexp::Star _args) -> bool { return false; }},
                *x);
          },
          [&](const regexp::Eps _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return false; },
                    [&](const regexp::Char _args) -> bool { return false; },
                    [&](const regexp::Eps _args) -> bool { return true; },
                    [&](const regexp::Cat _args) -> bool { return false; },
                    [&](const regexp::Alt _args) -> bool { return false; },
                    [&](const regexp::Zero _args) -> bool { return false; },
                    [&](const regexp::Star _args) -> bool { return false; }},
                *x);
          },
          [&](const regexp::Cat _args) -> T1 {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return false; },
                    [&](const regexp::Char _args) -> bool { return false; },
                    [&](const regexp::Eps _args) -> bool { return false; },
                    [&](const regexp::Cat _args) -> bool {
                      std::shared_ptr<regexp::regexp> r3 = _args._a0;
                      std::shared_ptr<regexp::regexp> r4 = _args._a1;
                      if (regexp_eq(r1, r3)) {
                        if (regexp_eq(r2, r4)) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [&](const regexp::Alt _args) -> bool { return false; },
                    [&](const regexp::Zero _args) -> bool { return false; },
                    [&](const regexp::Star _args) -> bool { return false; }},
                *x);
          },
          [&](const regexp::Alt _args) -> T1 {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return false; },
                    [&](const regexp::Char _args) -> bool { return false; },
                    [&](const regexp::Eps _args) -> bool { return false; },
                    [&](const regexp::Cat _args) -> bool { return false; },
                    [&](const regexp::Alt _args) -> bool {
                      std::shared_ptr<regexp::regexp> r3 = _args._a0;
                      std::shared_ptr<regexp::regexp> r4 = _args._a1;
                      if (regexp_eq(r1, r3)) {
                        if (regexp_eq(r2, r4)) {
                          return true;
                        } else {
                          return false;
                        }
                      } else {
                        return false;
                      }
                    },
                    [&](const regexp::Zero _args) -> bool { return false; },
                    [&](const regexp::Star _args) -> bool { return false; }},
                *x);
          },
          [&](const regexp::Zero _args) -> T1 {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return false; },
                    [&](const regexp::Char _args) -> bool { return false; },
                    [&](const regexp::Eps _args) -> bool { return false; },
                    [&](const regexp::Cat _args) -> bool { return false; },
                    [&](const regexp::Alt _args) -> bool { return false; },
                    [&](const regexp::Zero _args) -> bool { return true; },
                    [&](const regexp::Star _args) -> bool { return false; }},
                *x);
          },
          [&](const regexp::Star _args) -> T1 {
            std::shared_ptr<regexp::regexp> r0 = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args) -> bool { return false; },
                    [&](const regexp::Char _args) -> bool { return false; },
                    [&](const regexp::Eps _args) -> bool { return false; },
                    [&](const regexp::Cat _args) -> bool { return false; },
                    [&](const regexp::Alt _args) -> bool { return false; },
                    [&](const regexp::Zero _args) -> bool { return false; },
                    [&](const regexp::Star _args) -> bool {
                      std::shared_ptr<regexp::regexp> r1 = _args._a0;
                      if (regexp_eq(r0, r1)) {
                        return true;
                      } else {
                        return false;
                      }
                    }},
                *x);
          }},
      *r);
}

std::shared_ptr<regexp::regexp>
OptCat(const std::shared_ptr<regexp::regexp> r1,
       const std::shared_ptr<regexp::regexp> r2) {
  return std::visit(
      Overloaded{
          [&](const regexp::Any _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Zero::make();
                    },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    }},
                *r2);
          },
          [&](const regexp::Char _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Zero::make();
                    },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    }},
                *r2);
          },
          [&](const regexp::Eps _args) -> std::shared_ptr<regexp::regexp> {
            return r2;
          },
          [&](const regexp::Cat _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Zero::make();
                    },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    }},
                *r2);
          },
          [&](const regexp::Alt _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Zero::make();
                    },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    }},
                *r2);
          },
          [&](const regexp::Zero _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Zero::make();
          },
          [&](const regexp::Star _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Zero::make();
                    },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      return regexp::Cat::make(r1, r2);
                    }},
                *r2);
          }},
      *r1);
}

std::shared_ptr<regexp::regexp>
OptAlt(const std::shared_ptr<regexp::regexp> r1,
       const std::shared_ptr<regexp::regexp> r2) {
  return std::visit(
      Overloaded{
          [&](const regexp::Any _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    }},
                *r2);
          },
          [&](const regexp::Char _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    }},
                *r2);
          },
          [&](const regexp::Eps _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    }},
                *r2);
          },
          [&](const regexp::Cat _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    }},
                *r2);
          },
          [&](const regexp::Alt _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    }},
                *r2);
          },
          [&](const regexp::Zero _args) -> std::shared_ptr<regexp::regexp> {
            return r2;
          },
          [&](const regexp::Star _args) -> std::shared_ptr<regexp::regexp> {
            return std::visit(
                Overloaded{
                    [&](const regexp::Any _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Char _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Eps _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Cat _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Alt _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    },
                    [&](const regexp::Zero _args)
                        -> std::shared_ptr<regexp::regexp> { return r1; },
                    [&](const regexp::Star _args)
                        -> std::shared_ptr<regexp::regexp> {
                      if (regexp_eq(r1, r2)) {
                        return r1;
                      } else {
                        return regexp::Alt::make(r1, r2);
                      }
                    }},
                *r2);
          }},
      *r1);
}

std::shared_ptr<regexp::regexp> null(const std::shared_ptr<regexp::regexp> r) {
  return std::visit(
      Overloaded{
          [&](const regexp::Any _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Zero::make();
          },
          [&](const regexp::Char _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Zero::make();
          },
          [&](const regexp::Eps _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Eps::make();
          },
          [&](const regexp::Cat _args) -> std::shared_ptr<regexp::regexp> {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return OptCat(null(r1), null(r2));
          },
          [&](const regexp::Alt _args) -> std::shared_ptr<regexp::regexp> {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return OptAlt(null(r1), null(r2));
          },
          [&](const regexp::Zero _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Zero::make();
          },
          [&](const regexp::Star _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Eps::make();
          }},
      *r);
}

bool accepts_null(const std::shared_ptr<regexp::regexp> r) {
  return regexp_eq(null(r), regexp::Eps::make());
}

std::shared_ptr<regexp::regexp> deriv(const std::shared_ptr<regexp::regexp> r,
                                      const int c) {
  return std::visit(
      Overloaded{
          [&](const regexp::Any _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Eps::make();
          },
          [&](const regexp::Char _args) -> std::shared_ptr<regexp::regexp> {
            int c_ = _args._a0;
            if (char_eq(c, c_)) {
              return regexp::Eps::make();
            } else {
              return regexp::Zero::make();
            }
          },
          [&](const regexp::Eps _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Zero::make();
          },
          [&](const regexp::Cat _args) -> std::shared_ptr<regexp::regexp> {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return OptAlt(OptCat(deriv(r1, c), r2),
                          OptCat(null(r1), deriv(r2, c)));
          },
          [&](const regexp::Alt _args) -> std::shared_ptr<regexp::regexp> {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return OptAlt(deriv(r1, c), deriv(r2, c));
          },
          [&](const regexp::Zero _args) -> std::shared_ptr<regexp::regexp> {
            return regexp::Zero::make();
          },
          [&](const regexp::Star _args) -> std::shared_ptr<regexp::regexp> {
            std::shared_ptr<regexp::regexp> r0 = _args._a0;
            return OptCat(deriv(r0, c), regexp::Star::make(r0));
          }},
      *r);
}

std::shared_ptr<regexp::regexp>
derivs(const std::shared_ptr<regexp::regexp> r,
       const std::shared_ptr<list::list<int>> cs) {
  return std::visit(
      Overloaded{
          [&](const list::nil<int> _args) -> std::shared_ptr<regexp::regexp> {
            return r;
          },
          [&](const list::cons<int> _args) -> std::shared_ptr<regexp::regexp> {
            int c = _args._a0;
            std::shared_ptr<list::list<int>> cs_ = _args._a1;
            return derivs(deriv(r, c), cs_);
          }},
      *cs);
}

bool deriv_parse(const std::shared_ptr<regexp::regexp> r,
                 const std::shared_ptr<list::list<int>> cs) {
  if (accepts_null(derivs(r, cs))) {
    return true;
  } else {
    return false;
  }
}

bool NullEpsOrZero(const std::shared_ptr<regexp::regexp> r) {
  return std::visit(
      Overloaded{[&](const regexp::Any _args) -> T1 { return false; },
                 [&](const regexp::Char _args) -> T1 { return false; },
                 [&](const regexp::Eps _args) -> T1 { return true; },
                 [&](const regexp::Cat _args) -> T1 {
                   std::shared_ptr<regexp::regexp> r1 = _args._a0;
                   std::shared_ptr<regexp::regexp> r2 = _args._a1;
                   if (NullEpsOrZero(r1)) {
                     if (NullEpsOrZero(r2)) {
                       return true;
                     } else {
                       return false;
                     }
                   } else {
                     if (NullEpsOrZero(r2)) {
                       return false;
                     } else {
                       return false;
                     }
                   }
                 },
                 [&](const regexp::Alt _args) -> T1 {
                   std::shared_ptr<regexp::regexp> r1 = _args._a0;
                   std::shared_ptr<regexp::regexp> r2 = _args._a1;
                   if (NullEpsOrZero(r1)) {
                     if (NullEpsOrZero(r2)) {
                       return true;
                     } else {
                       return true;
                     }
                   } else {
                     if (NullEpsOrZero(r2)) {
                       return true;
                     } else {
                       return false;
                     }
                   }
                 },
                 [&](const regexp::Zero _args) -> T1 { return false; },
                 [&](const regexp::Star _args) -> T1 { return true; }},
      *r);
}

bool parse(const std::shared_ptr<regexp::regexp> r,
           const std::shared_ptr<list::list<int>> cs) {
  bool b = deriv_parse(r, cs);
  if (b) {
    return true;
  } else {
    return false;
  }
}

bool parse_bool(const std::shared_ptr<regexp::regexp> r,
                const std::shared_ptr<list::list<int>> cs) {
  if (parse(r, cs)) {
    return true;
  } else {
    return false;
  }
}

}; // namespace Matcher
