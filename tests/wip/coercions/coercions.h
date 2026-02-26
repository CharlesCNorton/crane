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

struct Coercions {
  static unsigned int bool_to_nat(const bool b);

  static unsigned int add_bool(const unsigned int n, const bool b);

  static inline const unsigned int test_add_true =
      add_bool((((((0 + 1) + 1) + 1) + 1) + 1), true);

  static inline const unsigned int test_add_false =
      add_bool((((((0 + 1) + 1) + 1) + 1) + 1), false);

  struct wrapper {
  public:
    struct mkWrapper {
      unsigned int _a0;
    };
    using variant_t = std::variant<mkWrapper>;

  private:
    variant_t v_;
    explicit wrapper(mkWrapper _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<wrapper> mkWrapper_(unsigned int a0) {
        return std::shared_ptr<wrapper>(new wrapper(mkWrapper{a0}));
      }
      static std::unique_ptr<wrapper> mkWrapper_uptr(unsigned int a0) {
        return std::unique_ptr<wrapper>(new wrapper(mkWrapper{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static unsigned int unwrap(std::shared_ptr<wrapper> w);

  static unsigned int double_wrapped(const std::shared_ptr<wrapper> &w);

  static inline const unsigned int test_double_wrapped =
      double_wrapped((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  struct boolBox {
  public:
    struct mkBoolBox {
      bool _a0;
    };
    using variant_t = std::variant<mkBoolBox>;

  private:
    variant_t v_;
    explicit boolBox(mkBoolBox _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<boolBox> mkBoolBox_(bool a0) {
        return std::shared_ptr<boolBox>(new boolBox(mkBoolBox{a0}));
      }
      static std::unique_ptr<boolBox> mkBoolBox_uptr(bool a0) {
        return std::unique_ptr<boolBox>(new boolBox(mkBoolBox{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static bool unbox(std::shared_ptr<boolBox> b);

  static unsigned int add_boolbox(const unsigned int n,
                                  const std::shared_ptr<boolBox> &bb);

  static inline const unsigned int test_add_boolbox = add_boolbox(
      ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), true);

  struct transform {
  public:
    struct mkTransform {
      std::function<unsigned int(unsigned int)> _a0;
    };
    using variant_t = std::variant<mkTransform>;

  private:
    variant_t v_;
    explicit transform(mkTransform _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<transform>
      mkTransform_(std::function<unsigned int(unsigned int)> a0) {
        return std::shared_ptr<transform>(new transform(mkTransform{a0}));
      }
      static std::unique_ptr<transform>
      mkTransform_uptr(std::function<unsigned int(unsigned int)> a0) {
        return std::unique_ptr<transform>(new transform(mkTransform{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static unsigned int apply_transform(const std::shared_ptr<transform> &,
                                      const unsigned int);

  static inline const std::shared_ptr<transform> double_transform =
      [](unsigned int n) { return (n + n); };

  static inline const unsigned int test_fun_coercion =
      double_transform((((((0 + 1) + 1) + 1) + 1) + 1));
};
