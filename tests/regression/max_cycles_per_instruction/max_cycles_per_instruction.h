#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  template <MapsTo<bool, A> F0> bool forallb(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> bool { return true; },
            [&](const typename List<A>::cons _args) -> bool {
              A a = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              return (f(a) && std::move(l0)->forallb(f));
            }},
        this->v());
  }
};

struct MaxCyclesPerInstruction {
  enum class instr {
    NOP,
    ADD,
    WRM,
    FIM,
    JMS,
    JCNTaken,
    JCNNotTaken,
    ISZTaken,
    ISZZero
  };

  template <typename T1>
  static T1 instr_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                       const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                       const T1 f7, const instr i) {
    return [&](void) {
      switch (i) {
      case instr::NOP: {
        return f;
      }
      case instr::ADD: {
        return f0;
      }
      case instr::WRM: {
        return f1;
      }
      case instr::FIM: {
        return f2;
      }
      case instr::JMS: {
        return f3;
      }
      case instr::JCNTaken: {
        return f4;
      }
      case instr::JCNNotTaken: {
        return f5;
      }
      case instr::ISZTaken: {
        return f6;
      }
      case instr::ISZZero: {
        return f7;
      }
      }
    }();
  }

  template <typename T1>
  static T1 instr_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                      const T1 f3, const T1 f4, const T1 f5, const T1 f6,
                      const T1 f7, const instr i) {
    return [&](void) {
      switch (i) {
      case instr::NOP: {
        return f;
      }
      case instr::ADD: {
        return f0;
      }
      case instr::WRM: {
        return f1;
      }
      case instr::FIM: {
        return f2;
      }
      case instr::JMS: {
        return f3;
      }
      case instr::JCNTaken: {
        return f4;
      }
      case instr::JCNNotTaken: {
        return f5;
      }
      case instr::ISZTaken: {
        return f6;
      }
      case instr::ISZZero: {
        return f7;
      }
      }
    }();
  }

  static unsigned int cycles(const instr i);

  static inline const std::shared_ptr<List<instr>> all_instrs =
      List<instr>::ctor::cons_(
          instr::NOP,
          List<instr>::ctor::cons_(
              instr::ADD,
              List<instr>::ctor::cons_(
                  instr::WRM,
                  List<instr>::ctor::cons_(
                      instr::FIM,
                      List<instr>::ctor::cons_(
                          instr::JMS,
                          List<instr>::ctor::cons_(
                              instr::JCNTaken,
                              List<instr>::ctor::cons_(
                                  instr::JCNNotTaken,
                                  List<instr>::ctor::cons_(
                                      instr::ISZTaken,
                                      List<instr>::ctor::cons_(
                                          instr::ISZZero,
                                          List<instr>::ctor::nil_())))))))));

  static inline const bool t = all_instrs->forallb([](instr i) {
    return (
        cycles(i) <=
        ((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
         1));
  });
};
