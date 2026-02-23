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

unsigned int bool_to_nat(const bool b);

unsigned int add_bool(const unsigned int n, const bool b);

const unsigned int test_add_true =
    add_bool((((((0 + 1) + 1) + 1) + 1) + 1), true);

const unsigned int test_add_false =
    add_bool((((((0 + 1) + 1) + 1) + 1) + 1), false);

struct Wrapper {
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
      static std::shared_ptr<Wrapper::wrapper> mkWrapper_(unsigned int a0) {
        return std::shared_ptr<Wrapper::wrapper>(
            new Wrapper::wrapper(mkWrapper{a0}));
      }
      static std::unique_ptr<Wrapper::wrapper> mkWrapper_uptr(unsigned int a0) {
        return std::unique_ptr<Wrapper::wrapper>(
            new Wrapper::wrapper(mkWrapper{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int unwrap() const { return this; }
    unsigned int double_wrapped() const { return (this + this); }
  };
};

const unsigned int test_double_wrapped =
    (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)->double_wrapped();

struct BoolBox {
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
      static std::shared_ptr<BoolBox::boolBox> mkBoolBox_(bool a0) {
        return std::shared_ptr<BoolBox::boolBox>(
            new BoolBox::boolBox(mkBoolBox{a0}));
      }
      static std::unique_ptr<BoolBox::boolBox> mkBoolBox_uptr(bool a0) {
        return std::unique_ptr<BoolBox::boolBox>(
            new BoolBox::boolBox(mkBoolBox{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    bool unbox() const { return this; }
    unsigned int add_boolbox(const unsigned int n) const {
      return (n + bool_to_nat(this));
    }
  };
};

const unsigned int test_add_boolbox = true->add_boolbox(
    ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));

struct Transform {
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
      static std::shared_ptr<Transform::transform>
      mkTransform_(std::function<unsigned int(unsigned int)> a0) {
        return std::shared_ptr<Transform::transform>(
            new Transform::transform(mkTransform{a0}));
      }
      static std::unique_ptr<Transform::transform>
      mkTransform_uptr(std::function<unsigned int(unsigned int)> a0) {
        return std::unique_ptr<Transform::transform>(
            new Transform::transform(mkTransform{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int apply_transform() const { return this; }
  };
};

const std::shared_ptr<Transform::transform> double_transform =
    [](unsigned int n) { return (n + n); };

const unsigned int test_fun_coercion =
    double_transform((((((0 + 1) + 1) + 1) + 1) + 1));
