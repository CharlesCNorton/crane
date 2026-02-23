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

bool eqb(const bool b1, const bool b2);

struct EqType {
  struct eqType {
  public:
    struct mkEqType {
      std::function<bool(std::any, std::any)> _a0;
    };
    using variant_t = std::variant<mkEqType>;

  private:
    variant_t v_;
    explicit eqType(mkEqType _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<EqType::eqType>
      mkEqType_(std::function<bool(std::any, std::any)> a0) {
        return std::shared_ptr<EqType::eqType>(
            new EqType::eqType(mkEqType{a0}));
      }
      static std::unique_ptr<EqType::eqType>
      mkEqType_uptr(std::function<bool(std::any, std::any)> a0) {
        return std::unique_ptr<EqType::eqType>(
            new EqType::eqType(mkEqType{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

using carrier = std::any;

const std::shared_ptr<EqType::eqType> nat_eqType =
    [](const unsigned int _x0, const unsigned int _x1) { return (_x0 == _x1); };

const std::shared_ptr<EqType::eqType> bool_eqType = eqb;

const bool test_nat =
    nat_eqType->same((((0 + 1) + 1) + 1), (((((0 + 1) + 1) + 1) + 1) + 1));

const bool test_bool = bool_eqType->same(true, false);
