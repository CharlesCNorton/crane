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
  A nth(const unsigned int n, const A default0) const {
    if (n <= 0) {
      return std::visit(Overloaded{[&](const typename List<A>::nil _args) -> A {
                                     return default0;
                                   },
                                   [](const typename List<A>::cons _args) -> A {
                                     A x = _args._a0;
                                     return x;
                                   }},
                        this->v());
    } else {
      unsigned int m = n - 1;
      return std::visit(
          Overloaded{
              [&](const typename List<A>::nil _args) -> A { return default0; },
              [&](const typename List<A>::cons _args) -> A {
                std::shared_ptr<List<A>> l_ = _args._a1;
                return std::move(l_)->nth(m, default0);
              }},
          this->v());
    }
  }
};

struct RamWriteFrameDifferentChip {
  template <typename T1>
  static std::shared_ptr<List<T1>>
  update_nth(const unsigned int n, const T1 x,
             const std::shared_ptr<List<T1>> &l) {
    if (n <= 0) {
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     std::shared_ptr<List<T1>> xs = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         x, std::move(xs));
                                   }},
                        l->v());
    } else {
      unsigned int n_ = n - 1;
      return std::visit(Overloaded{[](const typename List<T1>::nil _args)
                                       -> std::shared_ptr<List<T1>> {
                                     return List<T1>::ctor::nil_();
                                   },
                                   [&](const typename List<T1>::cons _args)
                                       -> std::shared_ptr<List<T1>> {
                                     T1 y = _args._a0;
                                     std::shared_ptr<List<T1>> ys = _args._a1;
                                     return List<T1>::ctor::cons_(
                                         y,
                                         update_nth<T1>(n_, x, std::move(ys)));
                                   }},
                        l->v());
    }
  }

  using reg = std::shared_ptr<List<unsigned int>>;

  using chip = std::shared_ptr<List<reg>>;

  using bank = std::shared_ptr<List<chip>>;

  static reg upd_main_in_reg(const std::shared_ptr<List<unsigned int>> &rg,
                             const unsigned int i, const unsigned int v);

  static chip upd_reg_in_chip(
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch,
      const unsigned int r, const std::shared_ptr<List<unsigned int>> &rg);

  static bank upd_chip_in_bank(
      const std::shared_ptr<
          List<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>> &bk,
      const unsigned int c,
      const std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> &ch);

  static inline const bank sample_bank = List<
      std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>::ctor::
      cons_(List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
                List<unsigned int>::ctor::cons_(
                    1u, List<unsigned int>::ctor::cons_(
                            2u, List<unsigned int>::ctor::cons_(
                                    3u, List<unsigned int>::ctor::nil_()))),
                List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
                    List<unsigned int>::ctor::cons_(
                        4u, List<unsigned int>::ctor::cons_(
                                5u, List<unsigned int>::ctor::cons_(
                                        6u, List<unsigned int>::ctor::nil_()))),
                    List<std::shared_ptr<List<unsigned int>>>::ctor::nil_())),
            List<std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>>>::
                ctor::cons_(
                    List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
                        List<unsigned int>::ctor::cons_(
                            7u,
                            List<unsigned int>::ctor::cons_(
                                8u, List<unsigned int>::ctor::cons_(
                                        9u, List<unsigned int>::ctor::nil_()))),
                        List<std::shared_ptr<List<unsigned int>>>::ctor::cons_(
                            List<unsigned int>::ctor::cons_(
                                10u,
                                List<unsigned int>::ctor::cons_(
                                    11u,
                                    List<unsigned int>::ctor::cons_(
                                        12u,
                                        List<unsigned int>::ctor::nil_()))),
                            List<std::shared_ptr<List<unsigned int>>>::ctor::
                                nil_())),
                    List<std::shared_ptr<List<
                        std::shared_ptr<List<unsigned int>>>>>::ctor::nil_()));

  static inline const bank updated_bank = [](void) {
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ch =
        sample_bank->nth(
            0u, List<std::shared_ptr<List<unsigned int>>>::ctor::nil_());
    std::shared_ptr<List<unsigned int>> rg =
        std::move(ch)->nth(1u, List<unsigned int>::ctor::nil_());
    std::shared_ptr<List<unsigned int>> rg_ =
        upd_main_in_reg(std::move(rg), 2u, 99u);
    std::shared_ptr<List<std::shared_ptr<List<unsigned int>>>> ch_ =
        upd_reg_in_chip(std::move(ch), 1u, std::move(rg_));
    return upd_chip_in_bank(sample_bank, 0u, std::move(ch_));
  }();

  static inline const bool t =
      (updated_bank
           ->nth(1u, List<std::shared_ptr<List<unsigned int>>>::ctor::nil_())
           ->nth(0u, List<unsigned int>::ctor::nil_())
           ->nth(2u, 0u) == 7u);
};
