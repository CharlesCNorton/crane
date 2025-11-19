#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

namespace List {
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

template <typename T1, typename T2,
          MapsTo<T2, T1, std::shared_ptr<list::list<T1>>, T2> F1>
T2 list_rect(const T2 f, F1 &&f0, const std::shared_ptr<list::list<T1>> l) {
  return std::visit(
      Overloaded{[&](const list::nil<T1> _args) -> T2 { return f; },
                 [&](const list::cons<T1> _args) -> T2 {
                   T1 y = _args._a0;
                   std::shared_ptr<list::list<T1>> l0 = _args._a1;
                   return f0(y, l0, list_rect<T1, T2>(f, f0, l0));
                 }},
      *l);
}

template <typename T1, typename T2,
          MapsTo<T2, T1, std::shared_ptr<list::list<T1>>, T2> F1>
T2 list_rec(const T2 f, F1 &&f0, const std::shared_ptr<list::list<T1>> l) {
  return std::visit(
      Overloaded{[&](const list::nil<T1> _args) -> T2 { return f; },
                 [&](const list::cons<T1> _args) -> T2 {
                   T1 y = _args._a0;
                   std::shared_ptr<list::list<T1>> l0 = _args._a1;
                   return f0(y, l0, list_rec<T1, T2>(f, f0, l0));
                 }},
      *l);
}

template <typename T1>
std::shared_ptr<list::list<T1>> tl(const std::shared_ptr<list::list<T1>> l) {
  return std::visit(
      Overloaded{
          [&](const list::nil<T1> _args) -> std::shared_ptr<list::list<T1>> {
            return list::nil<T1>::make();
          },
          [&](const list::cons<T1> _args) -> std::shared_ptr<list::list<T1>> {
            std::shared_ptr<list::list<T1>> ls = _args._a1;
            return ls;
          }},
      *l);
}

template <typename T1>
T1 hd(const T1 x, const std::shared_ptr<list::list<T1>> l) {
  return std::visit(
      Overloaded{[&](const list::nil<T1> _args) -> T1 { return x; },
                 [&](const list::cons<T1> _args) -> T1 {
                   T1 y = _args._a0;
                   return y;
                 }},
      *l);
}

template <typename T1>
T1 last(const T1 x, const std::shared_ptr<list::list<T1>> l) {
  return std::visit(
      Overloaded{[&](const list::nil<T1> _args) -> T1 { return x; },
                 [&](const list::cons<T1> _args) -> T1 {
                   T1 y = _args._a0;
                   std::shared_ptr<list::list<T1>> ls = _args._a1;
                   return last<T1>(y, ls);
                 }},
      *l);
}

template <typename T1>
std::shared_ptr<list::list<T1>> app(const std::shared_ptr<list::list<T1>> l1,
                                    const std::shared_ptr<list::list<T1>> l2) {
  return std::visit(
      Overloaded{
          [&](const list::nil<T1> _args) -> std::shared_ptr<list::list<T1>> {
            return l2;
          },
          [&](const list::cons<T1> _args) -> std::shared_ptr<list::list<T1>> {
            T1 x = _args._a0;
            std::shared_ptr<list::list<T1>> l3 = _args._a1;
            return list::cons<T1>::make(x, app<T1>(l3, l2));
          }},
      *l1);
}

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::shared_ptr<list::list<T2>> map(F0 &&f,
                                    const std::shared_ptr<list::list<T1>> l) {
  return std::visit(
      Overloaded{
          [&](const list::nil<T1> _args) -> std::shared_ptr<list::list<T2>> {
            return list::nil<T2>::make();
          },
          [&](const list::cons<T1> _args) -> std::shared_ptr<list::list<T2>> {
            T1 x = _args._a0;
            std::shared_ptr<list::list<T1>> l_ = _args._a1;
            return list::cons<T2>::make(f(x), map<T1, T2>(f, l_));
          }},
      *l);
}

const std::shared_ptr<list::list<unsigned int>> mytest = app<unsigned int>(
    list::cons<unsigned int>::make(
        3u, list::cons<unsigned int>::make(
                1u, list::cons<unsigned int>::make(
                        2u, list::nil<unsigned int>::make()))),
    list::cons<unsigned int>::make(
        8u, list::cons<unsigned int>::make(
                3u, list::cons<unsigned int>::make(
                        7u, list::cons<unsigned int>::make(
                                9u, list::nil<unsigned int>::make())))));

}; // namespace List
