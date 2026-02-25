#include <algorithm>
#include <any>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <persistent_array.h>
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

struct ConstrainedPoly {
  template <typename T1> static T1 poly_id(const T1 x) { return x; }

  template <typename A, typename B> struct UPair {
    A ufst;
    B usnd;
  };

  template <typename T1, typename T2>
  static T1 ufst(const std::shared_ptr<UPair<T1, T2>> &u) {
    return u->ufst;
  }

  template <typename T1, typename T2>
  static T2 usnd(const std::shared_ptr<UPair<T1, T2>> &u) {
    return u->usnd;
  }

  template <typename T1, typename T2>
  static std::shared_ptr<UPair<T2, T1>> swap(std::shared_ptr<UPair<T1, T2>> p) {
    return std::make_shared<UPair<T2, T1>>(UPair<T2, T1>{p->usnd, p->ufst});
  }

  template <typename T1, typename T2>
  static std::shared_ptr<UPair<T1, T2>> wrap_pair(const T1 a, const T2 b) {
    return std::make_shared<UPair<T1, T2>>(UPair<T1, T2>{a, b});
  }

  template <typename A> struct uOption {
  public:
    struct USome {
      A _a0;
    };
    struct UNone {};
    using variant_t = std::variant<USome, UNone>;

  private:
    variant_t v_;
    explicit uOption(USome _v) : v_(std::move(_v)) {}
    explicit uOption(UNone _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<uOption<A>> USome_(A a0) {
        return std::shared_ptr<uOption<A>>(new uOption<A>(USome{a0}));
      }
      static std::shared_ptr<uOption<A>> UNone_() {
        return std::shared_ptr<uOption<A>>(new uOption<A>(UNone{}));
      }
      static std::unique_ptr<uOption<A>> USome_uptr(A a0) {
        return std::unique_ptr<uOption<A>>(new uOption<A>(USome{a0}));
      }
      static std::unique_ptr<uOption<A>> UNone_uptr() {
        return std::unique_ptr<uOption<A>>(new uOption<A>(UNone{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rect(F0 &&f, const T2 f0,
                         const std::shared_ptr<uOption<T1>> &u) {
    return std::visit(
        Overloaded{
            [&](const typename uOption<T1>::USome _args) -> T2 {
              T1 a = _args._a0;
              return f(a);
            },
            [&](const typename uOption<T1>::UNone _args) -> T2 { return f0; }},
        u->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 UOption_rec(F0 &&f, const T2 f0,
                        const std::shared_ptr<uOption<T1>> &u) {
    return std::visit(
        Overloaded{
            [&](const typename uOption<T1>::USome _args) -> T2 {
              T1 a = _args._a0;
              return f(a);
            },
            [&](const typename uOption<T1>::UNone _args) -> T2 { return f0; }},
        u->v());
  }

  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static std::shared_ptr<uOption<T2>>
  uoption_map(F0 &&f, const std::shared_ptr<uOption<T1>> &o) {
    return std::visit(Overloaded{[&](const typename uOption<T1>::USome _args)
                                     -> std::shared_ptr<uOption<T2>> {
                                   T1 x = _args._a0;
                                   return uOption<T2>::ctor::USome_(f(x));
                                 },
                                 [](const typename uOption<T1>::UNone _args)
                                     -> std::shared_ptr<uOption<T2>> {
                                   return uOption<T2>::ctor::UNone_();
                                 }},
                      o->v());
  }

  static inline const unsigned int test_id_nat = poly_id<unsigned int>((
      (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
      1));

  static inline const bool test_id_bool = poly_id<bool>(true);

  static inline const std::shared_ptr<UPair<unsigned int, bool>> test_pair =
      wrap_pair<unsigned int, bool>((((((0 + 1) + 1) + 1) + 1) + 1), false);

  static inline const std::shared_ptr<UPair<bool, unsigned int>> test_swap =
      swap<unsigned int, bool>(test_pair);

  static inline const unsigned int test_fst = test_pair->ufst;

  static inline const bool test_snd = test_pair->usnd;

  static inline const std::shared_ptr<uOption<unsigned int>> test_umap =
      uoption_map<unsigned int, unsigned int>(
          [](unsigned int n) { return (n + (0 + 1)); },
          uOption<unsigned int>::ctor::USome_(
              (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)));
};
