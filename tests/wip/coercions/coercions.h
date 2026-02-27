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

  struct Wrapper {
  public:
    struct mkWrapper {
      unsigned int _a0;
    };
    using variant_t = std::variant<mkWrapper>;

  private:
    variant_t v_;
    explicit Wrapper(mkWrapper _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Wrapper> mkWrapper_(unsigned int a0) {
        return std::shared_ptr<Wrapper>(new Wrapper(mkWrapper{a0}));
      }
      static std::unique_ptr<Wrapper> mkWrapper_uptr(unsigned int a0) {
        return std::unique_ptr<Wrapper>(new Wrapper(mkWrapper{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static unsigned int unwrap(std::shared_ptr<Wrapper> w);

  static unsigned int double_wrapped(const std::shared_ptr<Wrapper> &w);

  static inline const unsigned int test_double_wrapped =
      double_wrapped((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1));

  struct BoolBox {
  public:
    struct mkBoolBox {
      bool _a0;
    };
    using variant_t = std::variant<mkBoolBox>;

  private:
    variant_t v_;
    explicit BoolBox(mkBoolBox _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<BoolBox> mkBoolBox_(bool a0) {
        return std::shared_ptr<BoolBox>(new BoolBox(mkBoolBox{a0}));
      }
      static std::unique_ptr<BoolBox> mkBoolBox_uptr(bool a0) {
        return std::unique_ptr<BoolBox>(new BoolBox(mkBoolBox{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static bool unbox(std::shared_ptr<BoolBox> b);

  static unsigned int add_boolbox(const unsigned int n,
                                  const std::shared_ptr<BoolBox> &bb);

  static inline const unsigned int test_add_boolbox = add_boolbox(
      ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1), true);

  struct Transform {
  public:
    struct mkTransform {
      std::function<unsigned int(unsigned int)> _a0;
    };
    using variant_t = std::variant<mkTransform>;

  private:
    variant_t v_;
    explicit Transform(mkTransform _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Transform>
      mkTransform_(std::function<unsigned int(unsigned int)> a0) {
        return std::shared_ptr<Transform>(new Transform(mkTransform{a0}));
      }
      static std::unique_ptr<Transform>
      mkTransform_uptr(std::function<unsigned int(unsigned int)> a0) {
        return std::unique_ptr<Transform>(new Transform(mkTransform{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static unsigned int apply_transform(const std::shared_ptr<Transform> &,
                                      const unsigned int);

  static inline const std::shared_ptr<Transform> double_transform =
      [](unsigned int n) { return (n + n); };

  static inline const unsigned int test_fun_coercion =
      double_transform((((((0 + 1) + 1) + 1) + 1) + 1));
};
