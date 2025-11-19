#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

namespace list {
template <typename A> struct nil;
template <typename A> struct cons;
template <typename A> using list = std::variant<nil<A>, cons<A>>;
template <typename A> struct nil {
  static std::shared_ptr<list<A>> make() {
    return std::make_shared<list<A>>(nil<A>{});
  }
};
template <typename A> struct cons {
  A _a0;
  std::shared_ptr<list<A>> _a1;
  static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
    return std::make_shared<list<A>>(cons<A>{_a0, _a1});
  }
};
}; // namespace list

namespace Matcher {
bool char_eq(const int x, const int y);

namespace regexp {
struct Any;
struct Char;
struct Eps;
struct Cat;
struct Alt;
struct Zero;
struct Star;
using regexp = std::variant<Any, Char, Eps, Cat, Alt, Zero, Star>;
struct Any {
  static std::shared_ptr<regexp> make();
};
struct Char {
  int _a0;
  static std::shared_ptr<regexp> make(int _a0);
};
struct Eps {
  static std::shared_ptr<regexp> make();
};
struct Cat {
  std::shared_ptr<regexp> _a0;
  std::shared_ptr<regexp> _a1;
  static std::shared_ptr<regexp> make(std::shared_ptr<regexp> _a0,
                                      std::shared_ptr<regexp> _a1);
};
struct Alt {
  std::shared_ptr<regexp> _a0;
  std::shared_ptr<regexp> _a1;
  static std::shared_ptr<regexp> make(std::shared_ptr<regexp> _a0,
                                      std::shared_ptr<regexp> _a1);
};
struct Zero {
  static std::shared_ptr<regexp> make();
};
struct Star {
  std::shared_ptr<regexp> _a0;
  static std::shared_ptr<regexp> make(std::shared_ptr<regexp> _a0);
};
}; // namespace regexp

template <typename T1, MapsTo<T1, int> F1,
          MapsTo<T1, std::shared_ptr<regexp::regexp>, T1,
                 std::shared_ptr<regexp::regexp>, T1>
              F3,
          MapsTo<T1, std::shared_ptr<regexp::regexp>, T1,
                 std::shared_ptr<regexp::regexp>, T1>
              F4,
          MapsTo<T1, std::shared_ptr<regexp::regexp>, T1> F6>
T1 regexp_rect(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3, const T1 f4,
               F6 &&f5, const std::shared_ptr<regexp::regexp> r) {
  return std::visit(
      Overloaded{
          [&](const regexp::Any _args) -> T1 { return f; },
          [&](const regexp::Char _args) -> T1 {
            int c = _args._a0;
            return f0(c);
          },
          [&](const regexp::Eps _args) -> T1 { return f1; },
          [&](const regexp::Cat _args) -> T1 {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return f2(r1, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                      regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2));
          },
          [&](const regexp::Alt _args) -> T1 {
            std::shared_ptr<regexp::regexp> r1 = _args._a0;
            std::shared_ptr<regexp::regexp> r2 = _args._a1;
            return f3(r1, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                      regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2));
          },
          [&](const regexp::Zero _args) -> T1 { return f4; },
          [&](const regexp::Star _args) -> T1 {
            std::shared_ptr<regexp::regexp> r0 = _args._a0;
            return f5(r0, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r0));
          }},
      *r);
}

template <typename T1, MapsTo<T1, int> F1,
          MapsTo<T1, std::shared_ptr<regexp::regexp>, T1,
                 std::shared_ptr<regexp::regexp>, T1>
              F3,
          MapsTo<T1, std::shared_ptr<regexp::regexp>, T1,
                 std::shared_ptr<regexp::regexp>, T1>
              F4,
          MapsTo<T1, std::shared_ptr<regexp::regexp>, T1> F6>
T1 regexp_rec(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3, const T1 f4,
              F6 &&f5, const std::shared_ptr<regexp::regexp> r) {
  return std::visit(
      Overloaded{[&](const regexp::Any _args) -> T1 { return f; },
                 [&](const regexp::Char _args) -> T1 {
                   int c = _args._a0;
                   return f0(c);
                 },
                 [&](const regexp::Eps _args) -> T1 { return f1; },
                 [&](const regexp::Cat _args) -> T1 {
                   std::shared_ptr<regexp::regexp> r1 = _args._a0;
                   std::shared_ptr<regexp::regexp> r2 = _args._a1;
                   return f2(r1, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r1),
                             r2, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2));
                 },
                 [&](const regexp::Alt _args) -> T1 {
                   std::shared_ptr<regexp::regexp> r1 = _args._a0;
                   std::shared_ptr<regexp::regexp> r2 = _args._a1;
                   return f3(r1, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r1),
                             r2, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2));
                 },
                 [&](const regexp::Zero _args) -> T1 { return f4; },
                 [&](const regexp::Star _args) -> T1 {
                   std::shared_ptr<regexp::regexp> r0 = _args._a0;
                   return f5(r0, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r0));
                 }},
      *r);
}

bool regexp_eq(const std::shared_ptr<regexp::regexp> r,
               const std::shared_ptr<regexp::regexp> x);

std::shared_ptr<regexp::regexp>
OptCat(const std::shared_ptr<regexp::regexp> r1,
       const std::shared_ptr<regexp::regexp> r2);

std::shared_ptr<regexp::regexp>
OptAlt(const std::shared_ptr<regexp::regexp> r1,
       const std::shared_ptr<regexp::regexp> r2);

std::shared_ptr<regexp::regexp> null(const std::shared_ptr<regexp::regexp> r);

bool accepts_null(const std::shared_ptr<regexp::regexp> r);

std::shared_ptr<regexp::regexp> deriv(const std::shared_ptr<regexp::regexp> r,
                                      const int c);

std::shared_ptr<regexp::regexp>
derivs(const std::shared_ptr<regexp::regexp> r,
       const std::shared_ptr<list::list<int>> cs);

bool deriv_parse(const std::shared_ptr<regexp::regexp> r,
                 const std::shared_ptr<list::list<int>> cs);

bool NullEpsOrZero(const std::shared_ptr<regexp::regexp> r);

bool parse(const std::shared_ptr<regexp::regexp> r,
           const std::shared_ptr<list::list<int>> cs);

bool parse_bool(const std::shared_ptr<regexp::regexp> r,
                const std::shared_ptr<list::list<int>> cs);

const std::shared_ptr<regexp::regexp> r1 = regexp::Cat::make(
    regexp::Star::make(regexp::Char::make(0)), regexp::Char::make(1));

const std::shared_ptr<list::list<int>> s1 =
    list::cons<int>::make(0, list::cons<int>::make(1, list::nil<int>::make()));

const std::shared_ptr<list::list<int>> s2 =
    list::cons<int>::make(1, list::nil<int>::make());

const std::shared_ptr<list::list<int>> s3 = list::cons<int>::make(
    0,
    list::cons<int>::make(0, list::cons<int>::make(1, list::nil<int>::make())));

const std::shared_ptr<list::list<int>> s4 =
    list::cons<int>::make(0, list::nil<int>::make());

}; // namespace Matcher
