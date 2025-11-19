#include <functional>
#include <iostream>
#include <levenshtein.h>
#include <memory>
#include <string>
#include <variant>

namespace bool0 {
std::shared_ptr<bool0> true0::make() {
  return std::make_shared<bool0>(true0{});
}
std::shared_ptr<bool0> false0::make() {
  return std::make_shared<bool0>(false0{});
}
}; // namespace bool0

namespace nat {
std::shared_ptr<nat> O::make() { return std::make_shared<nat>(O{}); }
std::shared_ptr<nat> S::make(std::shared_ptr<nat> _a0) {
  return std::make_shared<nat>(S{_a0});
}
}; // namespace nat

namespace sigT {};

namespace sumbool {
std::shared_ptr<sumbool> left::make() {
  return std::make_shared<sumbool>(left{});
}
std::shared_ptr<sumbool> right::make() {
  return std::make_shared<sumbool>(right{});
}
}; // namespace sumbool

std::shared_ptr<bool0::bool0> leb(const std::shared_ptr<nat::nat> n,
                                  const std::shared_ptr<nat::nat> m) {
  return std::visit(
      Overloaded{
          [&](const nat::O _args) -> std::shared_ptr<bool0::bool0> {
            return bool0::true0::make();
          },
          [&](const nat::S _args) -> std::shared_ptr<bool0::bool0> {
            std::shared_ptr<nat::nat> n_ = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const nat::O _args) -> std::shared_ptr<bool0::bool0> {
                      return bool0::false0::make();
                    },
                    [&](const nat::S _args) -> std::shared_ptr<bool0::bool0> {
                      std::shared_ptr<nat::nat> m_ = _args._a0;
                      return leb(n_, m_);
                    }},
                *m);
          }},
      *n);
}

std::shared_ptr<sumbool::sumbool>
bool_dec(const std::shared_ptr<bool0::bool0> b1,
         const std::shared_ptr<bool0::bool0> b2) {
  return std::visit(
      Overloaded{[&](const bool0::true0 _args) -> T1 {
                   return std::visit(
                       Overloaded{[&](const bool0::true0 _args)
                                      -> std::shared_ptr<sumbool::sumbool> {
                                    return sumbool::left::make();
                                  },
                                  [&](const bool0::false0 _args)
                                      -> std::shared_ptr<sumbool::sumbool> {
                                    return sumbool::right::make();
                                  }},
                       *b2);
                 },
                 [&](const bool0::false0 _args) -> T1 {
                   return std::visit(
                       Overloaded{[&](const bool0::true0 _args)
                                      -> std::shared_ptr<sumbool::sumbool> {
                                    return sumbool::right::make();
                                  },
                                  [&](const bool0::false0 _args)
                                      -> std::shared_ptr<sumbool::sumbool> {
                                    return sumbool::left::make();
                                  }},
                       *b2);
                 }},
      *b1);
}

namespace ascii {
std::shared_ptr<ascii> Ascii::make(
    std::shared_ptr<bool0::bool0> _a0, std::shared_ptr<bool0::bool0> _a1,
    std::shared_ptr<bool0::bool0> _a2, std::shared_ptr<bool0::bool0> _a3,
    std::shared_ptr<bool0::bool0> _a4, std::shared_ptr<bool0::bool0> _a5,
    std::shared_ptr<bool0::bool0> _a6, std::shared_ptr<bool0::bool0> _a7) {
  return std::make_shared<ascii>(Ascii{_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7});
}
}; // namespace ascii

std::shared_ptr<sumbool::sumbool>
ascii_dec(const std::shared_ptr<ascii::ascii> a,
          const std::shared_ptr<ascii::ascii> b) {
  return std::visit(
      Overloaded{
          [&](const ascii::Ascii _args) -> T1 {
            std::shared_ptr<bool0::bool0> b0 = _args._a0;
            std::shared_ptr<bool0::bool0> b1 = _args._a1;
            std::shared_ptr<bool0::bool0> b2 = _args._a2;
            std::shared_ptr<bool0::bool0> b3 = _args._a3;
            std::shared_ptr<bool0::bool0> b4 = _args._a4;
            std::shared_ptr<bool0::bool0> b5 = _args._a5;
            std::shared_ptr<bool0::bool0> b6 = _args._a6;
            std::shared_ptr<bool0::bool0> b7 = _args._a7;
            return std::visit(
                Overloaded{
                    [&](const ascii::Ascii _args)
                        -> std::shared_ptr<sumbool::sumbool> {
                      std::shared_ptr<bool0::bool0> b8 = _args._a0;
                      std::shared_ptr<bool0::bool0> b9 = _args._a1;
                      std::shared_ptr<bool0::bool0> b10 = _args._a2;
                      std::shared_ptr<bool0::bool0> b11 = _args._a3;
                      std::shared_ptr<bool0::bool0> b12 = _args._a4;
                      std::shared_ptr<bool0::bool0> b13 = _args._a5;
                      std::shared_ptr<bool0::bool0> b14 = _args._a6;
                      std::shared_ptr<bool0::bool0> b15 = _args._a7;
                      return std::visit(
                          Overloaded{
                              [&](const sumbool::left _args) -> T1 {
                                return std::visit(
                                    Overloaded{
                                        [&](const sumbool::left _args) -> T1 {
                                          return std::
                                              visit(
                                                  Overloaded{[&](const sumbool::
                                                                     left _args)
                                                                 -> T1 {
                                                               return std::visit(Overloaded{[&](const sumbool::
                                                                                                    left
                                                                                                        _args)
                                                                                                -> T1 {
                                                                                              return std::visit(Overloaded{
                                                                                                                    [&](const sumbool::
                                                                                                                            left
                                                                                                                                _args)
                                                                                                                        -> T1 {
                                                                                                                      return std::
                                                                                                                          visit(Overloaded{[&](const sumbool::
                                                                                                                                                   left
                                                                                                                                                       _args)
                                                                                                                                               -> T1 {
                                                                                                                                             return std::
                                                                                                                                                 visit(Overloaded{[&](const sumbool::
                                                                                                                                                                          left
                                                                                                                                                                              _args)
                                                                                                                                                                      -> T1 {
                                                                                                                                                                    return std::
                                                                                                                                                                        visit(Overloaded{[&](const sumbool::
                                                                                                                                                                                                 left
                                                                                                                                                                                                     _args)
                                                                                                                                                                                             -> T1 {
                                                                                                                                                                                           return sumbool::
                                                                                                                                                                                               left::
                                                                                                                                                                                                   make();
                                                                                                                                                                                         },
                                                                                                                                                                                         [&](const sumbool::right _args)
                                                                                                                                                                                             -> T1 {
                                                                                                                                                                                           return sumbool::
                                                                                                                                                                                               right::
                                                                                                                                                                                                   make();
                                                                                                                                                                                         }},
                                                                                                                                                                              *bool_dec(
                                                                                                                                                                                  b7,
                                                                                                                                                                                  b15));
                                                                                                                                                                  },
                                                                                                                                                                  [&](const sumbool::
                                                                                                                                                                          right
                                                                                                                                                                              _args)
                                                                                                                                                                      -> T1 {
                                                                                                                                                                    return sumbool::
                                                                                                                                                                        right::
                                                                                                                                                                            make();
                                                                                                                                                                  }},
                                                                                                                                                       *bool_dec(
                                                                                                                                                           b6,
                                                                                                                                                           b14));
                                                                                                                                           },
                                                                                                                                           [&](const sumbool::
                                                                                                                                                   right
                                                                                                                                                       _args)
                                                                                                                                               -> T1 {
                                                                                                                                             return sumbool::
                                                                                                                                                 right::
                                                                                                                                                     make();
                                                                                                                                           }},
                                                                                                                                *bool_dec(
                                                                                                                                    b5,
                                                                                                                                    b13));
                                                                                                                    },
                                                                                                                    [&](const sumbool::right _args) -> T1 {
                                                                                                                      return sumbool::
                                                                                                                          right::
                                                                                                                              make();
                                                                                                                    }},
                                                                                                                *bool_dec(
                                                                                                                    b4,
                                                                                                                    b12));
                                                                                            },
                                                                                            [&](const sumbool::
                                                                                                    right
                                                                                                        _args)
                                                                                                -> T1 {
                                                                                              return sumbool::
                                                                                                  right::
                                                                                                      make();
                                                                                            }},
                                                                                 *bool_dec(
                                                                                     b3,
                                                                                     b11));
                                                             },
                                                             [&](const sumbool::
                                                                     right
                                                                         _args)
                                                                 -> T1 {
                                                               return sumbool::
                                                                   right::
                                                                       make();
                                                             }},
                                                  *bool_dec(b2, b10));
                                        },
                                        [&](const sumbool::right _args) -> T1 {
                                          return sumbool::right::make();
                                        }},
                                    *bool_dec(b1, b9));
                              },
                              [&](const sumbool::right _args) -> T1 {
                                return sumbool::right::make();
                              }},
                          *bool_dec(b0, b8));
                    }},
                *b);
          }},
      *a);
}

namespace string {
std::shared_ptr<string> EmptyString::make() {
  return std::make_shared<string>(EmptyString{});
}
std::shared_ptr<string> String::make(std::shared_ptr<ascii::ascii> _a0,
                                     std::shared_ptr<string> _a1) {
  return std::make_shared<string>(String{_a0, _a1});
}
}; // namespace string

std::shared_ptr<nat::nat> length(const std::shared_ptr<string::string> s) {
  return std::visit(
      Overloaded{[&](const string::EmptyString _args)
                     -> std::shared_ptr<nat::nat> { return nat::O::make(); },
                 [&](const string::String _args) -> std::shared_ptr<nat::nat> {
                   std::shared_ptr<string::string> s_ = _args._a1;
                   return nat::S::make(length(s_));
                 }},
      *s);
}

namespace edit {
std::shared_ptr<edit> insertion::make(std::shared_ptr<ascii::ascii> _a0,
                                      std::shared_ptr<string::string> _a1) {
  return std::make_shared<edit>(insertion{_a0, _a1});
}
std::shared_ptr<edit> deletion::make(std::shared_ptr<ascii::ascii> _a0,
                                     std::shared_ptr<string::string> _a1) {
  return std::make_shared<edit>(deletion{_a0, _a1});
}
std::shared_ptr<edit> update::make(std::shared_ptr<ascii::ascii> _a0,
                                   std::shared_ptr<ascii::ascii> _a1,
                                   std::shared_ptr<string::string> _a2) {
  return std::make_shared<edit>(update{_a0, _a1, _a2});
}
}; // namespace edit

namespace chain {
std::shared_ptr<chain> empty::make() {
  return std::make_shared<chain>(empty{});
}
std::shared_ptr<chain> skip::make(std::shared_ptr<ascii::ascii> _a0,
                                  std::shared_ptr<string::string> _a1,
                                  std::shared_ptr<string::string> _a2,
                                  std::shared_ptr<nat::nat> _a3,
                                  std::shared_ptr<chain> _a4) {
  return std::make_shared<chain>(skip{_a0, _a1, _a2, _a3, _a4});
}
std::shared_ptr<chain> change::make(std::shared_ptr<string::string> _a0,
                                    std::shared_ptr<string::string> _a1,
                                    std::shared_ptr<string::string> _a2,
                                    std::shared_ptr<nat::nat> _a3,
                                    std::shared_ptr<edit::edit> _a4,
                                    std::shared_ptr<chain> _a5) {
  return std::make_shared<chain>(change{_a0, _a1, _a2, _a3, _a4, _a5});
}
}; // namespace chain

std::shared_ptr<chain::chain>
insert_chain(const std::shared_ptr<ascii::ascii> c,
             const std::shared_ptr<string::string> s1,
             const std::shared_ptr<string::string> s2,
             const std::shared_ptr<nat::nat> n,
             const std::shared_ptr<chain::chain> c0) {
  return chain::change::make(
      s1, string::String::make(c, s1), string::String::make(c, s2), n,
      edit::insertion::make(c, s1), chain::skip::make(c, s1, s2, n, c0));
}

std::shared_ptr<chain::chain>
inserts_chain_empty(const std::shared_ptr<string::string> s) {
  return std::visit(Overloaded{[&](const string::EmptyString _args) -> T1 {
                                 return chain::empty::make();
                               },
                               [&](const string::String _args) -> T1 {
                                 std::shared_ptr<ascii::ascii> a = _args._a0;
                                 std::shared_ptr<string::string> s0 = _args._a1;
                                 return insert_chain(
                                     a, string::EmptyString::make(), s0,
                                     length(s0), inserts_chain_empty(s0));
                               }},
                    *s);
}

std::shared_ptr<chain::chain>
delete_chain(const std::shared_ptr<ascii::ascii> c,
             const std::shared_ptr<string::string> s1,
             const std::shared_ptr<string::string> s2,
             const std::shared_ptr<nat::nat> n,
             const std::shared_ptr<chain::chain> c0) {
  return chain::change::make(string::String::make(c, s1), s1, s2, n,
                             edit::deletion::make(c, s1), c0);
}

std::shared_ptr<chain::chain>
deletes_chain_empty(const std::shared_ptr<string::string> s) {
  return std::visit(Overloaded{[&](const string::EmptyString _args) -> T1 {
                                 return chain::empty::make();
                               },
                               [&](const string::String _args) -> T1 {
                                 std::shared_ptr<ascii::ascii> a = _args._a0;
                                 std::shared_ptr<string::string> s0 = _args._a1;
                                 return delete_chain(
                                     a, s0, string::EmptyString::make(),
                                     length(s0), deletes_chain_empty(s0));
                               }},
                    *s);
}

std::shared_ptr<chain::chain>
update_chain(const std::shared_ptr<ascii::ascii> c,
             const std::shared_ptr<ascii::ascii> c_,
             const std::shared_ptr<string::string> s1,
             const std::shared_ptr<string::string> s2,
             const std::shared_ptr<nat::nat> n,
             const std::shared_ptr<chain::chain> c0) {
  return chain::change::make(
      string::String::make(c, s1), string::String::make(c_, s1),
      string::String::make(c_, s2), n, edit::update::make(c, c_, s1),
      chain::skip::make(c_, s1, s2, n, c0));
}

std::shared_ptr<chain::chain>
aux_insert(const std::shared_ptr<string::string> _x,
           const std::shared_ptr<string::string> _x0,
           const std::shared_ptr<ascii::ascii> x,
           const std::shared_ptr<string::string> xs,
           const std::shared_ptr<ascii::ascii> y,
           const std::shared_ptr<string::string> ys,
           const std::shared_ptr<nat::nat> n,
           const std::shared_ptr<chain::chain> r1) {
  return insert_chain(y, string::String::make(x, xs), ys, n, r1);
}

std::shared_ptr<chain::chain>
aux_delete(const std::shared_ptr<string::string> _x,
           const std::shared_ptr<string::string> _x0,
           const std::shared_ptr<ascii::ascii> x,
           const std::shared_ptr<string::string> xs,
           const std::shared_ptr<ascii::ascii> y,
           const std::shared_ptr<string::string> ys,
           const std::shared_ptr<nat::nat> n,
           const std::shared_ptr<chain::chain> r2) {
  return delete_chain(x, xs, string::String::make(y, ys), n, r2);
}

std::shared_ptr<chain::chain>
aux_update(const std::shared_ptr<string::string> _x,
           const std::shared_ptr<string::string> _x0,
           const std::shared_ptr<ascii::ascii> x,
           const std::shared_ptr<string::string> xs,
           const std::shared_ptr<ascii::ascii> y,
           const std::shared_ptr<string::string> ys,
           const std::shared_ptr<nat::nat> n,
           const std::shared_ptr<chain::chain> r3) {
  return update_chain(x, y, xs, ys, n, r3);
}

std::shared_ptr<chain::chain>
aux_eq_char(const std::shared_ptr<string::string> _x,
            const std::shared_ptr<string::string> _x0,
            const std::shared_ptr<ascii::ascii> _x1,
            const std::shared_ptr<string::string> xs,
            const std::shared_ptr<ascii::ascii> y,
            const std::shared_ptr<string::string> ys,
            const std::shared_ptr<nat::nat> n,
            const std::shared_ptr<chain::chain> c) {
  return chain::skip::make(y, xs, ys, n, c);
}

std::shared_ptr<chain::chain>
aux_both_empty(const std::shared_ptr<string::string> _x,
               const std::shared_ptr<string::string> _x0) {
  return chain::empty::make();
}

std::shared_ptr<
    sigT::sigT<std::shared_ptr<nat::nat>, std::shared_ptr<chain::chain>>>
levenshtein_chain(const std::shared_ptr<string::string> s,
                  const std::shared_ptr<string::string> _x0) {
  std::function<std::shared_ptr<
      sigT::sigT<std::shared_ptr<nat::nat>, std::shared_ptr<chain::chain>>>(
      std::shared_ptr<string::string>)>
      levenshtein_chain1;
  levenshtein_chain1 = [&](std::shared_ptr<string::string> t)
      -> std::shared_ptr<sigT::sigT<std::shared_ptr<nat::nat>,
                                    std::shared_ptr<chain::chain>>> {
    return std::visit(
        Overloaded{
            [&](const string::EmptyString _args)
                -> std::function<std::shared_ptr<sigT::sigT<
                    std::shared_ptr<nat::nat>, std::shared_ptr<chain::chain>>>(
                    dummy_prop, dummy_prop)> {
              return std::visit(
                  Overloaded{
                      [&](const string::EmptyString _args)
                          -> std::function<std::shared_ptr<
                              sigT::sigT<std::shared_ptr<nat::nat>,
                                         std::shared_ptr<chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        return sigT::existT<
                            std::shared_ptr<nat::nat>,
                            std::shared_ptr<chain::chain>>::make(nat::O::make(),
                                                                 aux_both_empty(
                                                                     _x0, t));
                      },
                      [&](const string::String _args)
                          -> std::function<std::shared_ptr<
                              sigT::sigT<std::shared_ptr<nat::nat>,
                                         std::shared_ptr<chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        return sigT::existT<std::shared_ptr<nat::nat>,
                                            std::shared_ptr<chain::chain>>::
                            make(length(t), inserts_chain_empty(t));
                      }},
                  *t);
            },
            [&](const string::String _args)
                -> std::function<std::shared_ptr<sigT::sigT<
                    std::shared_ptr<nat::nat>, std::shared_ptr<chain::chain>>>(
                    dummy_prop, dummy_prop)> {
              std::shared_ptr<ascii::ascii> x = _args._a0;
              std::shared_ptr<string::string> xs = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const string::EmptyString _args)
                          -> std::function<std::shared_ptr<
                              sigT::sigT<std::shared_ptr<nat::nat>,
                                         std::shared_ptr<chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        return sigT::existT<std::shared_ptr<nat::nat>,
                                            std::shared_ptr<chain::chain>>::
                            make(length(_x0), deletes_chain_empty(
                                                  string::String::make(x, xs)));
                      },
                      [&](const string::String _args)
                          -> std::function<std::shared_ptr<
                              sigT::sigT<std::shared_ptr<nat::nat>,
                                         std::shared_ptr<chain::chain>>>(
                              dummy_prop, dummy_prop)> {
                        std::shared_ptr<ascii::ascii> y = _args._a0;
                        std::shared_ptr<string::string> ys = _args._a1;
                        return std::visit(
                            Overloaded{
                                [&](const sumbool::left _args)
                                    -> std::shared_ptr<sigT::sigT<
                                        std::shared_ptr<nat::nat>,
                                        std::shared_ptr<chain::chain>>> {
                                  return std::visit(
                                      Overloaded{
                                          [&](const sigT::existT<
                                              std::shared_ptr<nat::nat>,
                                              std::shared_ptr<chain::chain>>
                                                  _args)
                                              -> std::shared_ptr<sigT::sigT<
                                                  std::shared_ptr<nat::nat>,
                                                  std::shared_ptr<
                                                      chain::chain>>> {
                                            std::shared_ptr<nat::nat> n =
                                                _args._a0;
                                            std::shared_ptr<chain::chain> c =
                                                _args._a1;
                                            return sigT::existT<
                                                std::shared_ptr<nat::nat>,
                                                std::shared_ptr<chain::chain>>::
                                                make(n,
                                                     aux_eq_char(_x0, t, x, xs,
                                                                 y, ys, n, c));
                                          }},
                                      *levenshtein_chain(xs, ys));
                                },
                                [&](const sumbool::right _args)
                                    -> std::shared_ptr<sigT::sigT<
                                        std::shared_ptr<nat::nat>,
                                        std::shared_ptr<chain::chain>>> {
                                  return std::visit(
                                      Overloaded{
                                          [&](const sigT::existT<
                                              std::shared_ptr<nat::nat>,
                                              std::shared_ptr<chain::chain>>
                                                  _args)
                                              -> std::shared_ptr<sigT::sigT<
                                                  std::shared_ptr<nat::nat>,
                                                  std::shared_ptr<
                                                      chain::chain>>> {
                                            std::shared_ptr<nat::nat> n1 =
                                                _args._a0;
                                            std::shared_ptr<chain::chain> r1 =
                                                _args._a1;
                                            return std::visit(
                                                Overloaded{
                                                    [&](const sigT::existT<
                                                        std::shared_ptr<
                                                            nat::nat>,
                                                        std::shared_ptr<
                                                            chain::chain>>
                                                            _args)
                                                        -> std::shared_ptr<
                                                            sigT::sigT<
                                                                std::shared_ptr<
                                                                    nat::nat>,
                                                                std::shared_ptr<
                                                                    chain::
                                                                        chain>>> {
                                                      std::shared_ptr<nat::nat>
                                                          n2 = _args._a0;
                                                      std::shared_ptr<
                                                          chain::chain>
                                                          r2 = _args._a1;
                                                      return std::visit(
                                                          Overloaded{[&](const sigT::existT<
                                                                         std::shared_ptr<
                                                                             nat::
                                                                                 nat>,
                                                                         std::shared_ptr<
                                                                             chain::
                                                                                 chain>>
                                                                             _args)
                                                                         -> std::
                                                                             shared_ptr<sigT::sigT<
                                                                                 std::shared_ptr<
                                                                                     nat::
                                                                                         nat>,
                                                                                 std::shared_ptr<chain::
                                                                                                     chain>>> {
                                                                               std::shared_ptr<
                                                                                   nat::
                                                                                       nat>
                                                                                   n3 =
                                                                                       _args
                                                                                           ._a0;
                                                                               std::shared_ptr<
                                                                                   chain::
                                                                                       chain>
                                                                                   r3 =
                                                                                       _args
                                                                                           ._a1;
                                                                               std::shared_ptr<
                                                                                   chain::
                                                                                       chain>
                                                                                   r1_ = aux_insert(
                                                                                       _x0,
                                                                                       t,
                                                                                       x,
                                                                                       xs,
                                                                                       y,
                                                                                       ys,
                                                                                       n1,
                                                                                       r1);
                                                                               std::shared_ptr<
                                                                                   chain::
                                                                                       chain>
                                                                                   r2_ = aux_delete(
                                                                                       _x0,
                                                                                       t,
                                                                                       x,
                                                                                       xs,
                                                                                       y,
                                                                                       ys,
                                                                                       n2,
                                                                                       r2);
                                                                               std::shared_ptr<
                                                                                   chain::
                                                                                       chain>
                                                                                   r3_ = aux_update(
                                                                                       _x0,
                                                                                       t,
                                                                                       x,
                                                                                       xs,
                                                                                       y,
                                                                                       ys,
                                                                                       n3,
                                                                                       r3);
                                                                               return min3_app<std::shared_ptr<
                                                                                   sigT::sigT<
                                                                                       std::shared_ptr<
                                                                                           nat::
                                                                                               nat>,
                                                                                       std::shared_ptr<
                                                                                           chain::
                                                                                               chain>>>>(
                                                                                   sigT::existT<
                                                                                       std::shared_ptr<
                                                                                           nat::
                                                                                               nat>,
                                                                                       std::shared_ptr<
                                                                                           chain::
                                                                                               chain>>::
                                                                                       make(
                                                                                           nat::S::make(
                                                                                               n1),
                                                                                           r1_),
                                                                                   sigT::existT<
                                                                                       std::shared_ptr<
                                                                                           nat::
                                                                                               nat>,
                                                                                       std::shared_ptr<
                                                                                           chain::
                                                                                               chain>>::
                                                                                       make(
                                                                                           nat::S::make(
                                                                                               n2),
                                                                                           r2_),
                                                                                   sigT::existT<
                                                                                       std::shared_ptr<
                                                                                           nat::
                                                                                               nat>,
                                                                                       std::shared_ptr<
                                                                                           chain::
                                                                                               chain>>::
                                                                                       make(
                                                                                           nat::S::make(
                                                                                               n3),
                                                                                           r3_),
                                                                                   projT1<std::shared_ptr<
                                                                                       nat::
                                                                                           nat>>);
                                                                             }},
                                                          *levenshtein_chain(
                                                              xs, ys));
                                                    }},
                                                *levenshtein_chain(
                                                    xs, string::String::make(
                                                            y, ys)));
                                          }},
                                      *levenshtein_chain1(ys));
                                }},
                            *ascii_dec(x, y));
                      }},
                  *t);
            }},
        *_x0);
  };
  return levenshtein_chain1(_x0);
}
