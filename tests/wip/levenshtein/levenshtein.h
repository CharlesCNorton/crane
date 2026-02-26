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

enum class bool0 { true0, false0 };

struct Nat {
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<Nat::nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O _v) : v_(std::move(_v)) {}
    explicit nat(S _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Nat::nat> O_() {
        return std::shared_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::shared_ptr<Nat::nat> S_(const std::shared_ptr<Nat::nat> &a0) {
        return std::shared_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
      static std::unique_ptr<Nat::nat> O_uptr() {
        return std::unique_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::unique_ptr<Nat::nat>
      S_uptr(const std::shared_ptr<Nat::nat> &a0) {
        return std::unique_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

struct SigT {
  template <typename A, typename P> struct sigT {
  public:
    struct existT {
      A _a0;
      P _a1;
    };
    using variant_t = std::variant<existT>;

  private:
    variant_t v_;
    explicit sigT(existT _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<SigT::sigT<A, P>> existT_(A a0, P a1) {
        return std::shared_ptr<SigT::sigT<A, P>>(
            new SigT::sigT<A, P>(existT{a0, a1}));
      }
      static std::unique_ptr<SigT::sigT<A, P>> existT_uptr(A a0, P a1) {
        return std::unique_ptr<SigT::sigT<A, P>>(
            new SigT::sigT<A, P>(existT{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    A projT1() const {
      return std::visit(
          Overloaded{[](const typename SigT::sigT<A, P>::existT _args) -> auto {
            A a = _args._a0;
            return a;
          }},
          this->v());
    }
  };
};

enum class sumbool { left, right };

bool0 leb(const std::shared_ptr<Nat::nat> &n,
          const std::shared_ptr<Nat::nat> &m);

sumbool bool_dec(const bool0 b1, const bool0 b2);

struct Ascii {
  struct ascii {
  public:
    struct Ascii {
      bool0 _a0;
      bool0 _a1;
      bool0 _a2;
      bool0 _a3;
      bool0 _a4;
      bool0 _a5;
      bool0 _a6;
      bool0 _a7;
    };
    using variant_t = std::variant<Ascii>;

  private:
    variant_t v_;
    explicit ascii(Ascii _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Ascii::ascii> Ascii_(bool0 a0, bool0 a1, bool0 a2,
                                                  bool0 a3, bool0 a4, bool0 a5,
                                                  bool0 a6, bool0 a7) {
        return std::shared_ptr<Ascii::ascii>(
            new Ascii::ascii(Ascii{a0, a1, a2, a3, a4, a5, a6, a7}));
      }
      static std::unique_ptr<Ascii::ascii> Ascii_uptr(bool0 a0, bool0 a1,
                                                      bool0 a2, bool0 a3,
                                                      bool0 a4, bool0 a5,
                                                      bool0 a6, bool0 a7) {
        return std::unique_ptr<Ascii::ascii>(
            new Ascii::ascii(Ascii{a0, a1, a2, a3, a4, a5, a6, a7}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    sumbool ascii_dec(const std::shared_ptr<Ascii::ascii> &b) const {
      return std::visit(
          Overloaded{[&](const typename Ascii::ascii::Ascii _args) -> auto {
            bool0 b0 = _args._a0;
            bool0 b1 = _args._a1;
            bool0 b2 = _args._a2;
            bool0 b3 = _args._a3;
            bool0 b4 = _args._a4;
            bool0 b5 = _args._a5;
            bool0 b6 = _args._a6;
            bool0 b7 = _args._a7;
            return std::visit(
                Overloaded{
                    [&](const typename Ascii::ascii::Ascii _args) -> sumbool {
                      bool0 b8 = _args._a0;
                      bool0 b9 = _args._a1;
                      bool0 b10 = _args._a2;
                      bool0 b11 = _args._a3;
                      bool0 b12 = _args._a4;
                      bool0 b13 = _args._a5;
                      bool0 b14 = _args._a6;
                      bool0 b15 = _args._a7;
                      return [&](void) {
                        switch (bool_dec(b0, b8)) {
                        case sumbool::left: {
                          return [&](void) {
                            switch (bool_dec(b1, b9)) {
                            case sumbool::left: {
                              return [&](void) {
                                switch (bool_dec(b2, b10)) {
                                case sumbool::left: {
                                  return [&](void) {
                                    switch (bool_dec(b3, b11)) {
                                    case sumbool::left: {
                                      return [&](void) {
                                        switch (bool_dec(b4, b12)) {
                                        case sumbool::left: {
                                          return [&](void) {
                                            switch (bool_dec(b5, b13)) {
                                            case sumbool::left: {
                                              return [&](void) {
                                                switch (bool_dec(b6, b14)) {
                                                case sumbool::left: {
                                                  return [&](void) {
                                                    switch (bool_dec(b7, b15)) {
                                                    case sumbool::left: {
                                                      return sumbool::left;
                                                    }
                                                    case sumbool::right: {
                                                      return sumbool::right;
                                                    }
                                                    }
                                                  }();
                                                }
                                                case sumbool::right: {
                                                  return sumbool::right;
                                                }
                                                }
                                              }();
                                            }
                                            case sumbool::right: {
                                              return sumbool::right;
                                            }
                                            }
                                          }();
                                        }
                                        case sumbool::right: {
                                          return sumbool::right;
                                        }
                                        }
                                      }();
                                    }
                                    case sumbool::right: {
                                      return sumbool::right;
                                    }
                                    }
                                  }();
                                }
                                case sumbool::right: {
                                  return sumbool::right;
                                }
                                }
                              }();
                            }
                            case sumbool::right: {
                              return sumbool::right;
                            }
                            }
                          }();
                        }
                        case sumbool::right: {
                          return sumbool::right;
                        }
                        }
                      }();
                    }},
                b->v());
          }},
          this->v());
    }
  };
};

struct String {
  struct string {
  public:
    struct EmptyString {};
    struct String {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
    };
    using variant_t = std::variant<EmptyString, String>;

  private:
    variant_t v_;
    explicit string(EmptyString _v) : v_(std::move(_v)) {}
    explicit string(String _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<String::string> EmptyString_() {
        return std::shared_ptr<String::string>(
            new String::string(EmptyString{}));
      }
      static std::shared_ptr<String::string>
      String_(const std::shared_ptr<Ascii::ascii> &a0,
              const std::shared_ptr<String::string> &a1) {
        return std::shared_ptr<String::string>(
            new String::string(String{a0, a1}));
      }
      static std::unique_ptr<String::string> EmptyString_uptr() {
        return std::unique_ptr<String::string>(
            new String::string(EmptyString{}));
      }
      static std::unique_ptr<String::string>
      String_uptr(const std::shared_ptr<Ascii::ascii> &a0,
                  const std::shared_ptr<String::string> &a1) {
        return std::unique_ptr<String::string>(
            new String::string(String{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    std::shared_ptr<String::string>
    append(const std::shared_ptr<String::string> &s2) const {
      return std::visit(
          Overloaded{[&](const typename String::string::EmptyString _args)
                         -> std::shared_ptr<String::string> { return s2; },
                     [&](const typename String::string::String _args)
                         -> std::shared_ptr<String::string> {
                       std::shared_ptr<Ascii::ascii> c = _args._a0;
                       std::shared_ptr<String::string> s1_ = _args._a1;
                       return String::string::ctor::String_(
                           std::move(c), std::move(s1_)->append(s2));
                     }},
          this->v());
    }
    std::shared_ptr<Nat::nat> length() const {
      return std::visit(
          Overloaded{
              [](const typename String::string::EmptyString _args)
                  -> std::shared_ptr<Nat::nat> { return Nat::nat::ctor::O_(); },
              [](const typename String::string::String _args)
                  -> std::shared_ptr<Nat::nat> {
                std::shared_ptr<String::string> s_ = _args._a1;
                return Nat::nat::ctor::S_(std::move(s_)->length());
              }},
          this->v());
    }
  };
};

struct Levenshtein {
  struct edit {
  public:
    struct insertion {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
    };
    struct deletion {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
    };
    struct update {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<Ascii::ascii> _a1;
      std::shared_ptr<String::string> _a2;
    };
    using variant_t = std::variant<insertion, deletion, update>;

  private:
    variant_t v_;
    explicit edit(insertion _v) : v_(std::move(_v)) {}
    explicit edit(deletion _v) : v_(std::move(_v)) {}
    explicit edit(update _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<edit>
      insertion_(const std::shared_ptr<Ascii::ascii> &a0,
                 const std::shared_ptr<String::string> &a1) {
        return std::shared_ptr<edit>(new edit(insertion{a0, a1}));
      }
      static std::shared_ptr<edit>
      deletion_(const std::shared_ptr<Ascii::ascii> &a0,
                const std::shared_ptr<String::string> &a1) {
        return std::shared_ptr<edit>(new edit(deletion{a0, a1}));
      }
      static std::shared_ptr<edit>
      update_(const std::shared_ptr<Ascii::ascii> &a0,
              const std::shared_ptr<Ascii::ascii> &a1,
              const std::shared_ptr<String::string> &a2) {
        return std::shared_ptr<edit>(new edit(update{a0, a1, a2}));
      }
      static std::unique_ptr<edit>
      insertion_uptr(const std::shared_ptr<Ascii::ascii> &a0,
                     const std::shared_ptr<String::string> &a1) {
        return std::unique_ptr<edit>(new edit(insertion{a0, a1}));
      }
      static std::unique_ptr<edit>
      deletion_uptr(const std::shared_ptr<Ascii::ascii> &a0,
                    const std::shared_ptr<String::string> &a1) {
        return std::unique_ptr<edit>(new edit(deletion{a0, a1}));
      }
      static std::unique_ptr<edit>
      update_uptr(const std::shared_ptr<Ascii::ascii> &a0,
                  const std::shared_ptr<Ascii::ascii> &a1,
                  const std::shared_ptr<String::string> &a2) {
        return std::unique_ptr<edit>(new edit(update{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<String::string>>
          F0,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<String::string>>
          F1,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<Ascii::ascii>,
             std::shared_ptr<String::string>>
          F2>
  static T1 edit_rect(F0 &&f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<String::string> &_x,
                      const std::shared_ptr<String::string> &_x0,
                      const std::shared_ptr<edit> &e) {
    return std::visit(
        Overloaded{[&](const typename edit::insertion _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s = _args._a1;
                     return f(std::move(a), std::move(s));
                   },
                   [&](const typename edit::deletion _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s = _args._a1;
                     return f0(std::move(a), std::move(s));
                   },
                   [&](const typename edit::update _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a_ = _args._a0;
                     std::shared_ptr<Ascii::ascii> a = _args._a1;
                     std::shared_ptr<String::string> s = _args._a2;
                     return f1(std::move(a_), std::move(a), "dummy",
                               std::move(s));
                   }},
        e->v());
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<String::string>>
          F0,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<String::string>>
          F1,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<Ascii::ascii>,
             std::shared_ptr<String::string>>
          F2>
  static T1 edit_rec(F0 &&f, F1 &&f0, F2 &&f1,
                     const std::shared_ptr<String::string> &_x,
                     const std::shared_ptr<String::string> &_x0,
                     const std::shared_ptr<edit> &e) {
    return std::visit(
        Overloaded{[&](const typename edit::insertion _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s = _args._a1;
                     return f(std::move(a), std::move(s));
                   },
                   [&](const typename edit::deletion _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s = _args._a1;
                     return f0(std::move(a), std::move(s));
                   },
                   [&](const typename edit::update _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a_ = _args._a0;
                     std::shared_ptr<Ascii::ascii> a = _args._a1;
                     std::shared_ptr<String::string> s = _args._a2;
                     return f1(std::move(a_), std::move(a), "dummy",
                               std::move(s));
                   }},
        e->v());
  }

  struct chain {
  public:
    struct empty {};
    struct skip {
      std::shared_ptr<Ascii::ascii> _a0;
      std::shared_ptr<String::string> _a1;
      std::shared_ptr<String::string> _a2;
      std::shared_ptr<Nat::nat> _a3;
      std::shared_ptr<chain> _a4;
    };
    struct change {
      std::shared_ptr<String::string> _a0;
      std::shared_ptr<String::string> _a1;
      std::shared_ptr<String::string> _a2;
      std::shared_ptr<Nat::nat> _a3;
      std::shared_ptr<edit> _a4;
      std::shared_ptr<chain> _a5;
    };
    using variant_t = std::variant<empty, skip, change>;

  private:
    variant_t v_;
    explicit chain(empty _v) : v_(std::move(_v)) {}
    explicit chain(skip _v) : v_(std::move(_v)) {}
    explicit chain(change _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<chain> empty_() {
        return std::shared_ptr<chain>(new chain(empty{}));
      }
      static std::shared_ptr<chain>
      skip_(const std::shared_ptr<Ascii::ascii> &a0,
            const std::shared_ptr<String::string> &a1,
            const std::shared_ptr<String::string> &a2,
            const std::shared_ptr<Nat::nat> &a3,
            const std::shared_ptr<chain> &a4) {
        return std::shared_ptr<chain>(new chain(skip{a0, a1, a2, a3, a4}));
      }
      static std::shared_ptr<chain>
      change_(const std::shared_ptr<String::string> &a0,
              const std::shared_ptr<String::string> &a1,
              const std::shared_ptr<String::string> &a2,
              const std::shared_ptr<Nat::nat> &a3,
              const std::shared_ptr<edit> &a4,
              const std::shared_ptr<chain> &a5) {
        return std::shared_ptr<chain>(
            new chain(change{a0, a1, a2, a3, a4, a5}));
      }
      static std::unique_ptr<chain> empty_uptr() {
        return std::unique_ptr<chain>(new chain(empty{}));
      }
      static std::unique_ptr<chain>
      skip_uptr(const std::shared_ptr<Ascii::ascii> &a0,
                const std::shared_ptr<String::string> &a1,
                const std::shared_ptr<String::string> &a2,
                const std::shared_ptr<Nat::nat> &a3,
                const std::shared_ptr<chain> &a4) {
        return std::unique_ptr<chain>(new chain(skip{a0, a1, a2, a3, a4}));
      }
      static std::unique_ptr<chain>
      change_uptr(const std::shared_ptr<String::string> &a0,
                  const std::shared_ptr<String::string> &a1,
                  const std::shared_ptr<String::string> &a2,
                  const std::shared_ptr<Nat::nat> &a3,
                  const std::shared_ptr<edit> &a4,
                  const std::shared_ptr<chain> &a5) {
        return std::unique_ptr<chain>(
            new chain(change{a0, a1, a2, a3, a4, a5}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<String::string>,
             std::shared_ptr<String::string>, std::shared_ptr<Nat::nat>,
             std::shared_ptr<chain>, T1>
          F1,
      MapsTo<T1, std::shared_ptr<String::string>,
             std::shared_ptr<String::string>, std::shared_ptr<String::string>,
             std::shared_ptr<Nat::nat>, std::shared_ptr<edit>,
             std::shared_ptr<chain>, T1>
          F2>
  static T1 chain_rect(const T1 f, F1 &&f0, F2 &&f1,
                       const std::shared_ptr<String::string> &_x,
                       const std::shared_ptr<String::string> &_x0,
                       const std::shared_ptr<Nat::nat> &_x1,
                       const std::shared_ptr<chain> &c) {
    return std::visit(
        Overloaded{[&](const typename chain::empty _args) -> T1 { return f; },
                   [&](const typename chain::skip _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s = _args._a1;
                     std::shared_ptr<String::string> t = _args._a2;
                     std::shared_ptr<Nat::nat> n = _args._a3;
                     std::shared_ptr<chain> c0 = _args._a4;
                     return f0(std::move(a), s, t, n, c0,
                               chain_rect<T1>(f, f0, f1, s, t, n, c0));
                   },
                   [&](const typename chain::change _args) -> T1 {
                     std::shared_ptr<String::string> s = _args._a0;
                     std::shared_ptr<String::string> t = _args._a1;
                     std::shared_ptr<String::string> u = _args._a2;
                     std::shared_ptr<Nat::nat> n = _args._a3;
                     std::shared_ptr<edit> e = _args._a4;
                     std::shared_ptr<chain> c0 = _args._a5;
                     return f1(std::move(s), t, u, n, std::move(e), c0,
                               chain_rect<T1>(f, f0, f1, t, u, n, c0));
                   }},
        c->v());
  }

  template <
      typename T1,
      MapsTo<T1, std::shared_ptr<Ascii::ascii>, std::shared_ptr<String::string>,
             std::shared_ptr<String::string>, std::shared_ptr<Nat::nat>,
             std::shared_ptr<chain>, T1>
          F1,
      MapsTo<T1, std::shared_ptr<String::string>,
             std::shared_ptr<String::string>, std::shared_ptr<String::string>,
             std::shared_ptr<Nat::nat>, std::shared_ptr<edit>,
             std::shared_ptr<chain>, T1>
          F2>
  static T1 chain_rec(const T1 f, F1 &&f0, F2 &&f1,
                      const std::shared_ptr<String::string> &_x,
                      const std::shared_ptr<String::string> &_x0,
                      const std::shared_ptr<Nat::nat> &_x1,
                      const std::shared_ptr<chain> &c) {
    return std::visit(
        Overloaded{[&](const typename chain::empty _args) -> T1 { return f; },
                   [&](const typename chain::skip _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s = _args._a1;
                     std::shared_ptr<String::string> t = _args._a2;
                     std::shared_ptr<Nat::nat> n = _args._a3;
                     std::shared_ptr<chain> c0 = _args._a4;
                     return f0(std::move(a), s, t, n, c0,
                               chain_rec<T1>(f, f0, f1, s, t, n, c0));
                   },
                   [&](const typename chain::change _args) -> T1 {
                     std::shared_ptr<String::string> s = _args._a0;
                     std::shared_ptr<String::string> t = _args._a1;
                     std::shared_ptr<String::string> u = _args._a2;
                     std::shared_ptr<Nat::nat> n = _args._a3;
                     std::shared_ptr<edit> e = _args._a4;
                     std::shared_ptr<chain> c0 = _args._a5;
                     return f1(std::move(s), t, u, n, std::move(e), c0,
                               chain_rec<T1>(f, f0, f1, t, u, n, c0));
                   }},
        c->v());
  }

  static std::shared_ptr<chain>
  same_chain(const std::shared_ptr<String::string> &s);

  static std::shared_ptr<chain> insert_chain(std::shared_ptr<Ascii::ascii> c,
                                             std::shared_ptr<String::string> s1,
                                             std::shared_ptr<String::string> s2,
                                             std::shared_ptr<Nat::nat> n,
                                             std::shared_ptr<chain> c0);

  template <typename T1>
  static T1 _inserts_chain_F(const std::shared_ptr<String::string> &s) {
    return std::visit(
        Overloaded{[](const typename String::string::EmptyString _args) -> T1 {
                     return chain::ctor::empty_();
                   },
                   [](const typename String::string::String _args) -> T1 {
                     std::shared_ptr<Ascii::ascii> a = _args._a0;
                     std::shared_ptr<String::string> s0 = _args._a1;
                     return chain::ctor::skip_(std::move(a), s0, s0,
                                               Nat::nat::ctor::O_(),
                                               _inserts_chain_F<T1>(s0));
                   }},
        s->v());
  }
  static std::shared_ptr<chain>
  inserts_chain(const std::shared_ptr<String::string> &s1,
                const std::shared_ptr<String::string> &s2);

  static std::shared_ptr<chain>
  inserts_chain_empty(const std::shared_ptr<String::string> &s);

  static std::shared_ptr<chain> delete_chain(std::shared_ptr<Ascii::ascii> c,
                                             std::shared_ptr<String::string> s1,
                                             std::shared_ptr<String::string> s2,
                                             std::shared_ptr<Nat::nat> n,
                                             std::shared_ptr<chain> c0);

  static std::shared_ptr<chain>
  deletes_chain(const std::shared_ptr<String::string> &s1,
                const std::shared_ptr<String::string> &s2);

  static std::shared_ptr<chain>
  deletes_chain_empty(const std::shared_ptr<String::string> &s);

  static std::shared_ptr<chain> update_chain(std::shared_ptr<Ascii::ascii> c,
                                             std::shared_ptr<Ascii::ascii> c_,
                                             std::shared_ptr<String::string> s1,
                                             std::shared_ptr<String::string> s2,
                                             std::shared_ptr<Nat::nat> n,
                                             std::shared_ptr<chain> c0);

  static std::shared_ptr<chain> aux_insert(
      const std::shared_ptr<String::string> &_x,
      const std::shared_ptr<String::string> &_x0,
      std::shared_ptr<Ascii::ascii> x, std::shared_ptr<String::string> xs,
      const std::shared_ptr<Ascii::ascii> &y,
      const std::shared_ptr<String::string> &ys,
      const std::shared_ptr<Nat::nat> &n, const std::shared_ptr<chain> &r1);

  static std::shared_ptr<chain> aux_delete(
      const std::shared_ptr<String::string> &_x,
      const std::shared_ptr<String::string> &_x0,
      const std::shared_ptr<Ascii::ascii> &x,
      const std::shared_ptr<String::string> &xs,
      std::shared_ptr<Ascii::ascii> y, std::shared_ptr<String::string> ys,
      const std::shared_ptr<Nat::nat> &n, const std::shared_ptr<chain> &r2);

  static std::shared_ptr<chain>
  aux_update(const std::shared_ptr<String::string> &_x,
             const std::shared_ptr<String::string> &_x0,
             const std::shared_ptr<Ascii::ascii> &x,
             const std::shared_ptr<String::string> &xs,
             const std::shared_ptr<Ascii::ascii> &y,
             const std::shared_ptr<String::string> &ys,
             const std::shared_ptr<Nat::nat> &n,
             const std::shared_ptr<chain> &r3);

  static std::shared_ptr<chain>
  aux_eq_char(const std::shared_ptr<String::string> &_x,
              const std::shared_ptr<String::string> &_x0,
              const std::shared_ptr<Ascii::ascii> &_x1,
              std::shared_ptr<String::string> xs,
              std::shared_ptr<Ascii::ascii> y,
              std::shared_ptr<String::string> ys, std::shared_ptr<Nat::nat> n,
              std::shared_ptr<chain> c);

  static std::shared_ptr<chain>
  aux_both_empty(const std::shared_ptr<String::string> &_x,
                 const std::shared_ptr<String::string> &_x0);

  template <typename T1, MapsTo<std::shared_ptr<Nat::nat>, T1> F3>
  static T1 min3_app(const T1 x, const T1 y, const T1 z, F3 &&f) {
    std::shared_ptr<Nat::nat> n1 = f(x);
    std::shared_ptr<Nat::nat> n2 = f(y);
    std::shared_ptr<Nat::nat> n3 = f(z);
    return [&](void) {
      switch (leb(n1, n2)) {
      case bool0::true0: {
        return [&](void) {
          switch (leb(std::move(n1), std::move(n3))) {
          case bool0::true0: {
            return x;
          }
          case bool0::false0: {
            return z;
          }
          }
        }();
      }
      case bool0::false0: {
        return [&](void) {
          switch (leb(std::move(n2), std::move(n3))) {
          case bool0::true0: {
            return y;
          }
          case bool0::false0: {
            return z;
          }
          }
        }();
      }
      }
    }();
  }

  static std::shared_ptr<
      SigT::sigT<std::shared_ptr<Nat::nat>, std::shared_ptr<chain>>>
  levenshtein_chain(const std::shared_ptr<String::string> &,
                    const std::shared_ptr<String::string> &);

  static std::shared_ptr<Nat::nat>
  levenshtein_computed(const std::shared_ptr<String::string> &s,
                       const std::shared_ptr<String::string> &t);

  static std::shared_ptr<Nat::nat>
  levenshtein(const std::shared_ptr<String::string> &,
              const std::shared_ptr<String::string> &);
};
