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

template <typename T1> T1 poly_id(const T1 x) { return x; }

template <typename A, typename B> struct UPair {
  A ufst;
  B usnd;
};

template <typename T1, typename T2>
std::shared_ptr<UPair<T1, T2>> wrap_pair(const T1 a, const T2 b) {
  return std::make_shared<UPair<T1, T2>>(UPair<T1, T2>{a, b});
}

struct UOption {
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
      static std::shared_ptr<UOption::uOption<A>> USome_(A a0) {
        return std::shared_ptr<UOption::uOption<A>>(
            new UOption::uOption<A>(USome{a0}));
      }
      static std::shared_ptr<UOption::uOption<A>> UNone_() {
        return std::shared_ptr<UOption::uOption<A>>(
            new UOption::uOption<A>(UNone{}));
      }
      static std::unique_ptr<UOption::uOption<A>> USome_uptr(A a0) {
        return std::unique_ptr<UOption::uOption<A>>(
            new UOption::uOption<A>(USome{a0}));
      }
      static std::unique_ptr<UOption::uOption<A>> UNone_uptr() {
        return std::unique_ptr<UOption::uOption<A>>(
            new UOption::uOption<A>(UNone{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<UOption::uOption<T2>> uoption_map(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename UOption::uOption<A>::USome _args)
                         -> std::shared_ptr<UOption::uOption<T2>> {
                       A x = _args._a0;
                       return UOption::uOption<T2>::ctor::USome_(f(x));
                     },
                     [](const typename UOption::uOption<A>::UNone _args)
                         -> std::shared_ptr<UOption::uOption<T2>> {
                       return UOption::uOption<T2>::ctor::UNone_();
                     }},
          this->v());
    }
  };
};

const unsigned int test_id_nat = poly_id<unsigned int>(
    ((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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

const bool test_id_bool = poly_id<bool>(true);

const std::shared_ptr<UPair<unsigned int, bool>> test_pair =
    wrap_pair<unsigned int, bool>((((((0 + 1) + 1) + 1) + 1) + 1), false);

const std::shared_ptr<UPair<bool, unsigned int>> test_swap = test_pair->swap();

const unsigned int test_fst = test_pair->ufst;

const bool test_snd = test_pair->usnd;

const std::shared_ptr<UOption::uOption<unsigned int>> test_umap =
    UOption::uOption<unsigned int>::ctor::USome_(
        (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1))
        ->uoption_map([](unsigned int n) { return (n + (0 + 1)); });
