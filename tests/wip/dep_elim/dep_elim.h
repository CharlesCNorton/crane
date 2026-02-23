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

struct Fin {
  struct fin {
  public:
    struct FZ {
      unsigned int _a0;
    };
    struct FS {
      unsigned int _a0;
      std::shared_ptr<Fin::fin> _a1;
    };
    using variant_t = std::variant<FZ, FS>;

  private:
    variant_t v_;
    explicit fin(FZ _v) : v_(std::move(_v)) {}
    explicit fin(FS _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Fin::fin> FZ_(unsigned int a0) {
        return std::shared_ptr<Fin::fin>(new Fin::fin(FZ{a0}));
      }
      static std::shared_ptr<Fin::fin>
      FS_(unsigned int a0, const std::shared_ptr<Fin::fin> &a1) {
        return std::shared_ptr<Fin::fin>(new Fin::fin(FS{a0, a1}));
      }
      static std::unique_ptr<Fin::fin> FZ_uptr(unsigned int a0) {
        return std::unique_ptr<Fin::fin>(new Fin::fin(FZ{a0}));
      }
      static std::unique_ptr<Fin::fin>
      FS_uptr(unsigned int a0, const std::shared_ptr<Fin::fin> &a1) {
        return std::unique_ptr<Fin::fin>(new Fin::fin(FS{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int fin_to_nat(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename Fin::fin::FZ _args) -> unsigned int {
                       return 0;
                     },
                     [](const typename Fin::fin::FS _args) -> unsigned int {
                       unsigned int n0 = _args._a0;
                       std::shared_ptr<Fin::fin> f_ = _args._a1;
                       return (std::move(f_)->fin_to_nat(std::move(n0)) + 1);
                     }},
          this->v());
    }
  };
};

struct Vec {
  template <typename A> struct vec {
  public:
    struct vnil {};
    struct vcons {
      unsigned int _a0;
      A _a1;
      std::shared_ptr<Vec::vec<A>> _a2;
    };
    using variant_t = std::variant<vnil, vcons>;

  private:
    variant_t v_;
    explicit vec(vnil _v) : v_(std::move(_v)) {}
    explicit vec(vcons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Vec::vec<A>> vnil_() {
        return std::shared_ptr<Vec::vec<A>>(new Vec::vec<A>(vnil{}));
      }
      static std::shared_ptr<Vec::vec<A>>
      vcons_(unsigned int a0, A a1, const std::shared_ptr<Vec::vec<A>> &a2) {
        return std::shared_ptr<Vec::vec<A>>(new Vec::vec<A>(vcons{a0, a1, a2}));
      }
      static std::unique_ptr<Vec::vec<A>> vnil_uptr() {
        return std::unique_ptr<Vec::vec<A>>(new Vec::vec<A>(vnil{}));
      }
      static std::unique_ptr<Vec::vec<A>>
      vcons_uptr(unsigned int a0, A a1,
                 const std::shared_ptr<Vec::vec<A>> &a2) {
        return std::unique_ptr<Vec::vec<A>>(new Vec::vec<A>(vcons{a0, a1, a2}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    std::shared_ptr<List::list<A>> vec_to_list(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename Vec::vec<A>::vnil _args)
                         -> std::shared_ptr<List::list<A>> {
                       return List::list<A>::ctor::nil_();
                     },
                     [](const typename Vec::vec<A>::vcons _args)
                         -> std::shared_ptr<List::list<A>> {
                       unsigned int n0 = _args._a0;
                       A x = _args._a1;
                       std::shared_ptr<Vec::vec<A>> xs = _args._a2;
                       return List::list<A>::ctor::cons_(
                           x, std::move(xs)->vec_to_list(std::move(n0)));
                     }},
          this->v());
    }
    template <typename T2, MapsTo<T2, A> F1>
    std::shared_ptr<Vec::vec<T2>> vec_map(const unsigned int _x, F1 &&f) const {
      return std::visit(
          Overloaded{[](const typename Vec::vec<A>::vnil _args)
                         -> std::shared_ptr<Vec::vec<T2>> {
                       return Vec::vec<T2>::ctor::vnil_();
                     },
                     [&](const typename Vec::vec<A>::vcons _args)
                         -> std::shared_ptr<Vec::vec<T2>> {
                       unsigned int n0 = _args._a0;
                       A x = _args._a1;
                       std::shared_ptr<Vec::vec<A>> xs = _args._a2;
                       return Vec::vec<T2>::ctor::vcons_(
                           n0, f(x), std::move(xs)->vec_map(n0, f));
                     }},
          this->v());
    }
    A vec_head(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename Vec::vec<A>::vnil _args) -> auto {
                       return "dummy";
                     },
                     [](const typename Vec::vec<A>::vcons _args) -> auto {
                       A x = _args._a1;
                       return x;
                     }},
          this->v());
    }
    std::shared_ptr<Vec::vec<A>> vec_tail(const unsigned int _x) const {
      return std::visit(
          Overloaded{[](const typename Vec::vec<A>::vnil _args)
                         -> std::shared_ptr<Vec::vec<A>> { return "dummy"; },
                     [](const typename Vec::vec<A>::vcons _args)
                         -> std::shared_ptr<Vec::vec<A>> {
                       std::shared_ptr<Vec::vec<A>> xs = _args._a2;
                       return std::move(xs);
                     }},
          this->v());
    }
  };
};

struct Avail {
  struct avail {
  public:
    struct present {
      unsigned int _a0;
    };
    struct absent {};
    using variant_t = std::variant<present, absent>;

  private:
    variant_t v_;
    explicit avail(present _v) : v_(std::move(_v)) {}
    explicit avail(absent _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Avail::avail> present_(unsigned int a0) {
        return std::shared_ptr<Avail::avail>(new Avail::avail(present{a0}));
      }
      static std::shared_ptr<Avail::avail> absent_() {
        return std::shared_ptr<Avail::avail>(new Avail::avail(absent{}));
      }
      static std::unique_ptr<Avail::avail> present_uptr(unsigned int a0) {
        return std::unique_ptr<Avail::avail>(new Avail::avail(present{a0}));
      }
      static std::unique_ptr<Avail::avail> absent_uptr() {
        return std::unique_ptr<Avail::avail>(new Avail::avail(absent{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int get_present() const {
      return std::visit(
          Overloaded{
              [](const typename Avail::avail::present _args) -> unsigned int {
                unsigned int n = _args._a0;
                return std::move(n);
              },
              [](const typename Avail::avail::absent _args) -> unsigned int {
                return "dummy";
              }},
          this->v());
    }
  };
};

const unsigned int test_fin0 =
    Fin::fin::ctor::FZ_(((0 + 1) + 1))->fin_to_nat((((0 + 1) + 1) + 1));

const unsigned int test_fin2 =
    Fin::fin::ctor::FS_(((0 + 1) + 1),
                        Fin::fin::ctor::FS_((0 + 1), Fin::fin::ctor::FZ_(0)))
        ->fin_to_nat((((0 + 1) + 1) + 1));

const std::shared_ptr<Vec::vec<unsigned int>> my_vec =
    Vec::vec<unsigned int>::ctor::vcons_(
        ((0 + 1) + 1),
        ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
        Vec::vec<unsigned int>::ctor::vcons_(
            (0 + 1),
            ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
            Vec::vec<unsigned int>::ctor::vcons_(
                0,
                ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
                Vec::vec<unsigned int>::ctor::vnil_())));

const std::shared_ptr<List::list<unsigned int>> test_vec_list =
    my_vec->vec_to_list((((0 + 1) + 1) + 1));

const unsigned int test_vec_head = my_vec->vec_head(((0 + 1) + 1));

const std::shared_ptr<List::list<unsigned int>> test_vec_tail_list =
    my_vec->vec_tail(((0 + 1) + 1))->vec_to_list(((0 + 1) + 1));

const std::shared_ptr<List::list<unsigned int>> test_vec_map =
    my_vec
        ->vec_map((((0 + 1) + 1) + 1),
                  [](unsigned int n) { return (n + (0 + 1)); })
        ->vec_to_list((((0 + 1) + 1) + 1));

const unsigned int test_present =
    Avail::avail::ctor::present_(
        ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) +
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
          1) +
         1))
        ->get_present();
