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

struct Bool {
  static bool eqb(const bool b1, const bool b2);
};

struct CanonStruct {
  struct EqType {
  public:
    struct mkEqType {
      std::function<bool(std::any, std::any)> _a0;
    };
    using variant_t = std::variant<mkEqType>;

  private:
    variant_t v_;
    explicit EqType(mkEqType _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<EqType>
      mkEqType_(std::function<bool(std::any, std::any)> a0) {
        return std::shared_ptr<EqType>(new EqType(mkEqType{a0}));
      }
      static std::unique_ptr<EqType>
      mkEqType_uptr(std::function<bool(std::any, std::any)> a0) {
        return std::unique_ptr<EqType>(new EqType(mkEqType{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  using carrier = std::any;

  static bool eqb(const std::shared_ptr<EqType> &, const carrier,
                  const carrier);

  static inline const std::shared_ptr<EqType> nat_eqType =
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 == _x1);
      };

  static inline const std::shared_ptr<EqType> bool_eqType = Bool::eqb;

  static bool same(const std::shared_ptr<EqType> &, const carrier,
                   const carrier);

  static inline const bool test_nat =
      same(nat_eqType, (((0 + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));

  static inline const bool test_bool = same(bool_eqType, true, false);
};
