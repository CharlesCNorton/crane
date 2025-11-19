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

namespace nat {
struct O;
struct S;
using nat = std::variant<O, S>;
struct O {
  static std::shared_ptr<nat> make();
};
struct S {
  std::shared_ptr<nat> _a0;
  static std::shared_ptr<nat> make(std::shared_ptr<nat> _a0);
};
}; // namespace nat

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

namespace Colist {
namespace colist {
template <typename A> struct conil;
template <typename A> struct cocons;
template <typename A> using colist = std::variant<conil<A>, cocons<A>>;
template <typename A> struct conil {
  static std::shared_ptr<colist<A>> make() {
    return std::make_shared<colist<A>>(conil<A>{});
  }
};
template <typename A> struct cocons {
  A _a0;
  std::shared_ptr<colist<A>> _a1;
  static std::shared_ptr<colist<A>> make(A _a0,
                                         std::shared_ptr<colist<A>> _a1) {
    return std::make_shared<colist<A>>(cocons<A>{_a0, _a1});
  }
};
}; // namespace colist

template <typename T1>
std::shared_ptr<list::list<T1>>
list_of_colist(const std::shared_ptr<nat::nat> fuel,
               const std::shared_ptr<colist::colist<T1>> l) {
  return std::visit(
      Overloaded{[&](const nat::O _args) -> std::shared_ptr<list::list<T1>> {
                   return list::nil<T1>::make();
                 },
                 [&](const nat::S _args) -> std::shared_ptr<list::list<T1>> {
                   std::shared_ptr<nat::nat> fuel_ = _args._a0;
                   return std::visit(
                       Overloaded{[&](const colist::conil<T1> _args)
                                      -> std::shared_ptr<list::list<T1>> {
                                    return list::nil<T1>::make();
                                  },
                                  [&](const colist::cocons<T1> _args)
                                      -> std::shared_ptr<list::list<T1>> {
                                    T1 x = _args._a0;
                                    std::shared_ptr<colist::colist<T1>> xs =
                                        _args._a1;
                                    return list::cons<T1>::make(
                                        x, list_of_colist<T1>(fuel_, xs));
                                  }},
                       *l);
                 }},
      *fuel);
}

std::shared_ptr<colist::colist<std::shared_ptr<nat::nat>>>
nats(const std::shared_ptr<nat::nat> n);

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::shared_ptr<colist::colist<T2>>
comap(F0 &&f, const std::shared_ptr<colist::colist<T1>> l) {
  return std::visit(
      Overloaded{[&](const colist::conil<T1> _args)
                     -> std::shared_ptr<colist::colist<T2>> {
                   return colist::conil<T2>::make();
                 },
                 [&](const colist::cocons<T1> _args)
                     -> std::shared_ptr<colist::colist<T2>> {
                   T1 x = _args._a0;
                   std::shared_ptr<colist::colist<T1>> xs = _args._a1;
                   return colist::cocons<T2>::make(f(x), comap<T1, T2>(f, xs));
                 }},
      *l);
}

const std::shared_ptr<list::list<std::shared_ptr<nat::nat>>> first_three =
    list_of_colist<std::shared_ptr<nat::nat>>(
        nat::S::make(nat::S::make(nat::S::make(nat::O::make()))),
        nats(nat::O::make()));

}; // namespace Colist
