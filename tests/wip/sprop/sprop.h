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

struct Nat {
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                                      const unsigned int y,
                                                      const unsigned int q,
                                                      const unsigned int u);

  static unsigned int div(const unsigned int x, const unsigned int y);
};

struct SPropTest {
  template <typename T1>
  static inline const T1 sFalse_rect =
      [](axiom _x) { throw std::logic_error("absurd case"); };

  template <typename T1>
  static inline const T1 sFalse_rec =
      [](axiom _x) { throw std::logic_error("absurd case"); };

  template <typename A> struct box {
  public:
    struct mkBox {
      A _a0;
    };
    using variant_t = std::variant<mkBox>;

  private:
    variant_t v_;
    explicit box(mkBox _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<box<A>> mkBox_(A a0) {
        return std::shared_ptr<box<A>>(new box<A>(mkBox{a0}));
      }
      static std::unique_ptr<box<A>> mkBox_uptr(A a0) {
        return std::unique_ptr<box<A>>(new box<A>(mkBox{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  template <typename T1> static T1 box_value(std::shared_ptr<box<T1>> b) {
    return std::move(b);
  }

  static unsigned int guarded_pred(const unsigned int n);

  static unsigned int safe_div(const unsigned int, const unsigned int);

  static inline const unsigned int test_guarded =
      guarded_pred((((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const unsigned int test_box =
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
       1);

  static inline const unsigned int test_div =
      safe_div(((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
               (((0 + 1) + 1) + 1));
};

std::pair<unsigned int, unsigned int> divmod(const unsigned int x,
                                             const unsigned int y,
                                             const unsigned int q,
                                             const unsigned int u);

unsigned int div(const unsigned int x, const unsigned int y);
