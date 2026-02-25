#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
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

enum class comparison { Eq, Lt, Gt };

struct Positive {
  struct positive {
  public:
    struct xI {
      std::shared_ptr<Positive::positive> _a0;
    };
    struct xO {
      std::shared_ptr<Positive::positive> _a0;
    };
    struct xH {};
    using variant_t = std::variant<xI, xO, xH>;

  private:
    variant_t v_;
    explicit positive(xI _v) : v_(std::move(_v)) {}
    explicit positive(xO _v) : v_(std::move(_v)) {}
    explicit positive(xH _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Positive::positive>
      xI_(const std::shared_ptr<Positive::positive> &a0) {
        return std::shared_ptr<Positive::positive>(
            new Positive::positive(xI{a0}));
      }
      static std::shared_ptr<Positive::positive>
      xO_(const std::shared_ptr<Positive::positive> &a0) {
        return std::shared_ptr<Positive::positive>(
            new Positive::positive(xO{a0}));
      }
      static std::shared_ptr<Positive::positive> xH_() {
        return std::shared_ptr<Positive::positive>(
            new Positive::positive(xH{}));
      }
      static std::unique_ptr<Positive::positive>
      xI_uptr(const std::shared_ptr<Positive::positive> &a0) {
        return std::unique_ptr<Positive::positive>(
            new Positive::positive(xI{a0}));
      }
      static std::unique_ptr<Positive::positive>
      xO_uptr(const std::shared_ptr<Positive::positive> &a0) {
        return std::unique_ptr<Positive::positive>(
            new Positive::positive(xO{a0}));
      }
      static std::unique_ptr<Positive::positive> xH_uptr() {
        return std::unique_ptr<Positive::positive>(
            new Positive::positive(xH{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

struct N {
  struct n {
  public:
    struct N0 {};
    struct Npos {
      std::shared_ptr<Positive::positive> _a0;
    };
    using variant_t = std::variant<N0, Npos>;

  private:
    variant_t v_;
    explicit n(N0 _v) : v_(std::move(_v)) {}
    explicit n(Npos _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<N::n> N0_() {
        return std::shared_ptr<N::n>(new N::n(N0{}));
      }
      static std::shared_ptr<N::n>
      Npos_(const std::shared_ptr<Positive::positive> &a0) {
        return std::shared_ptr<N::n>(new N::n(Npos{a0}));
      }
      static std::unique_ptr<N::n> N0_uptr() {
        return std::unique_ptr<N::n>(new N::n(N0{}));
      }
      static std::unique_ptr<N::n>
      Npos_uptr(const std::shared_ptr<Positive::positive> &a0) {
        return std::unique_ptr<N::n>(new N::n(Npos{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

struct Z {
  struct z {
  public:
    struct Z0 {};
    struct Zpos {
      std::shared_ptr<Positive::positive> _a0;
    };
    struct Zneg {
      std::shared_ptr<Positive::positive> _a0;
    };
    using variant_t = std::variant<Z0, Zpos, Zneg>;

  private:
    variant_t v_;
    explicit z(Z0 _v) : v_(std::move(_v)) {}
    explicit z(Zpos _v) : v_(std::move(_v)) {}
    explicit z(Zneg _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Z::z> Z0_() {
        return std::shared_ptr<Z::z>(new Z::z(Z0{}));
      }
      static std::shared_ptr<Z::z>
      Zpos_(const std::shared_ptr<Positive::positive> &a0) {
        return std::shared_ptr<Z::z>(new Z::z(Zpos{a0}));
      }
      static std::shared_ptr<Z::z>
      Zneg_(const std::shared_ptr<Positive::positive> &a0) {
        return std::shared_ptr<Z::z>(new Z::z(Zneg{a0}));
      }
      static std::unique_ptr<Z::z> Z0_uptr() {
        return std::unique_ptr<Z::z>(new Z::z(Z0{}));
      }
      static std::unique_ptr<Z::z>
      Zpos_uptr(const std::shared_ptr<Positive::positive> &a0) {
        return std::unique_ptr<Z::z>(new Z::z(Zpos{a0}));
      }
      static std::unique_ptr<Z::z>
      Zneg_uptr(const std::shared_ptr<Positive::positive> &a0) {
        return std::unique_ptr<Z::z>(new Z::z(Zneg{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

struct Pos {
  static std::shared_ptr<Positive::positive>
  succ(const std::shared_ptr<Positive::positive> &x);

  static std::shared_ptr<Positive::positive>
  add(const std::shared_ptr<Positive::positive> &x,
      const std::shared_ptr<Positive::positive> &y);
  static std::shared_ptr<Positive::positive>
  add_carry(const std::shared_ptr<Positive::positive> &x,
            const std::shared_ptr<Positive::positive> &y);

  static std::shared_ptr<Positive::positive>
  pred_double(const std::shared_ptr<Positive::positive> &x);

  static std::shared_ptr<N::n>
  pred_N(const std::shared_ptr<Positive::positive> &x);

  struct mask {
  public:
    struct IsNul {};
    struct IsPos {
      std::shared_ptr<Positive::positive> _a0;
    };
    struct IsNeg {};
    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    variant_t v_;
    explicit mask(IsNul _v) : v_(std::move(_v)) {}
    explicit mask(IsPos _v) : v_(std::move(_v)) {}
    explicit mask(IsNeg _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<mask> IsNul_() {
        return std::shared_ptr<mask>(new mask(IsNul{}));
      }
      static std::shared_ptr<mask>
      IsPos_(const std::shared_ptr<Positive::positive> &a0) {
        return std::shared_ptr<mask>(new mask(IsPos{a0}));
      }
      static std::shared_ptr<mask> IsNeg_() {
        return std::shared_ptr<mask>(new mask(IsNeg{}));
      }
      static std::unique_ptr<mask> IsNul_uptr() {
        return std::unique_ptr<mask>(new mask(IsNul{}));
      }
      static std::unique_ptr<mask>
      IsPos_uptr(const std::shared_ptr<Positive::positive> &a0) {
        return std::unique_ptr<mask>(new mask(IsPos{a0}));
      }
      static std::unique_ptr<mask> IsNeg_uptr() {
        return std::unique_ptr<mask>(new mask(IsNeg{}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };

  static std::shared_ptr<mask> succ_double_mask(const std::shared_ptr<mask> &x);

  static std::shared_ptr<mask> double_mask(const std::shared_ptr<mask> &x);

  static std::shared_ptr<mask>
  double_pred_mask(const std::shared_ptr<Positive::positive> &x);

  static std::shared_ptr<mask>
  sub_mask(const std::shared_ptr<Positive::positive> &x,
           const std::shared_ptr<Positive::positive> &y);
  static std::shared_ptr<mask>
  sub_mask_carry(const std::shared_ptr<Positive::positive> &x,
                 const std::shared_ptr<Positive::positive> &y);

  static std::shared_ptr<Positive::positive>
  mul(const std::shared_ptr<Positive::positive> &x,
      std::shared_ptr<Positive::positive> y);

  static comparison compare_cont(const comparison r,
                                 const std::shared_ptr<Positive::positive> &x,
                                 const std::shared_ptr<Positive::positive> &y);

  static comparison compare(const std::shared_ptr<Positive::positive> &,
                            const std::shared_ptr<Positive::positive> &);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive::positive> &p,
                    const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::positive::xI _args) -> T1 {
                     std::shared_ptr<Positive::positive> p0 = _args._a0;
                     return op(a, iter_op<T1>(op, std::move(p0), op(a, a)));
                   },
                   [&](const typename Positive::positive::xO _args) -> T1 {
                     std::shared_ptr<Positive::positive> p0 = _args._a0;
                     return iter_op<T1>(op, std::move(p0), op(a, a));
                   },
                   [&](const typename Positive::positive::xH _args) -> T1 {
                     return a;
                   }},
        p->v());
  }

  static unsigned int to_nat(const std::shared_ptr<Positive::positive> &x);
};

struct Coq_Pos {
  static std::shared_ptr<Positive::positive>
  succ(const std::shared_ptr<Positive::positive> &x);

  static std::shared_ptr<Positive::positive>
  add(const std::shared_ptr<Positive::positive> &x,
      const std::shared_ptr<Positive::positive> &y);
  static std::shared_ptr<Positive::positive>
  add_carry(const std::shared_ptr<Positive::positive> &x,
            const std::shared_ptr<Positive::positive> &y);

  static std::shared_ptr<Positive::positive>
  mul(const std::shared_ptr<Positive::positive> &x,
      std::shared_ptr<Positive::positive> y);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive::positive> &p,
                    const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::positive::xI _args) -> T1 {
                     std::shared_ptr<Positive::positive> p0 = _args._a0;
                     return op(a, iter_op<T1>(op, std::move(p0), op(a, a)));
                   },
                   [&](const typename Positive::positive::xO _args) -> T1 {
                     std::shared_ptr<Positive::positive> p0 = _args._a0;
                     return iter_op<T1>(op, std::move(p0), op(a, a));
                   },
                   [&](const typename Positive::positive::xH _args) -> T1 {
                     return a;
                   }},
        p->v());
  }

  static unsigned int to_nat(const std::shared_ptr<Positive::positive> &x);
};

struct N {
  static std::shared_ptr<N::n> sub(std::shared_ptr<N::n> n,
                                   const std::shared_ptr<N::n> &m);

  static comparison compare(const std::shared_ptr<N::n> &n,
                            const std::shared_ptr<N::n> &m);

  static std::shared_ptr<N::n> pred(const std::shared_ptr<N::n> &n);

  static std::shared_ptr<N::n> add(std::shared_ptr<N::n> n,
                                   std::shared_ptr<N::n> m);

  static std::shared_ptr<N::n> mul(const std::shared_ptr<N::n> &n,
                                   const std::shared_ptr<N::n> &m);

  static unsigned int to_nat(const std::shared_ptr<N::n> &a);
};

struct Z {
  static std::shared_ptr<Z::z> double(const std::shared_ptr<Z::z> &x);

  static std::shared_ptr<Z::z> succ_double(const std::shared_ptr<Z::z> &x);

  static std::shared_ptr<Z::z> pred_double(const std::shared_ptr<Z::z> &x);

  static std::shared_ptr<Z::z>
  pos_sub(const std::shared_ptr<Positive::positive> &x,
          const std::shared_ptr<Positive::positive> &y);

  static std::shared_ptr<Z::z> add(std::shared_ptr<Z::z> x,
                                   std::shared_ptr<Z::z> y);

  static std::shared_ptr<Z::z> opp(const std::shared_ptr<Z::z> &x);

  static std::shared_ptr<Z::z> sub(const std::shared_ptr<Z::z> &m,
                                   const std::shared_ptr<Z::z> &n);

  static std::shared_ptr<Z::z> mul(const std::shared_ptr<Z::z> &x,
                                   const std::shared_ptr<Z::z> &y);

  static comparison compare(const std::shared_ptr<Z::z> &x,
                            const std::shared_ptr<Z::z> &y);

  static unsigned int to_nat(const std::shared_ptr<Z::z> &z);

  static std::shared_ptr<Z::z> abs(const std::shared_ptr<Z::z> &z);
};

struct BinaryNums {
  static inline const std::shared_ptr<Positive::positive> pos_one =
      Positive::positive::ctor::xH_();

  static inline const std::shared_ptr<Positive::positive> pos_five =
      Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()));

  static inline const std::shared_ptr<Positive::positive> pos_add_result =
      Coq_Pos::add(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_()),
          Positive::positive::ctor::xI_(
              Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<Positive::positive> pos_mul_result =
      Coq_Pos::mul(Positive::positive::ctor::xO_(Positive::positive::ctor::xO_(
                       Positive::positive::ctor::xH_())),
                   Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
                       Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<Positive::positive> pos_succ_result =
      Coq_Pos::succ(Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))));

  static inline const std::shared_ptr<N::n> n_zero = N::n::ctor::N0_();

  static inline const std::shared_ptr<N::n> n_five =
      N::n::ctor::Npos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<N::n> n_add_result = N::add(
      N::n::ctor::Npos_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xI_(
              Positive::positive::ctor::xO_(Positive::positive::ctor::xH_())))),
      N::n::ctor::Npos_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xO_(
              Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
                  Positive::positive::ctor::xH_()))))));

  static inline const std::shared_ptr<N::n> n_mul_result = N::mul(
      N::n::ctor::Npos_(Positive::positive::ctor::xO_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_()))),
      N::n::ctor::Npos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_()))));

  static inline const std::shared_ptr<N::n> n_sub_result = N::sub(
      N::n::ctor::Npos_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xI_(
              Positive::positive::ctor::xO_(Positive::positive::ctor::xH_())))),
      N::n::ctor::Npos_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<N::n> n_pred_result =
      N::pred(N::n::ctor::Npos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))));

  static inline const comparison n_compare_result = N::compare(
      N::n::ctor::Npos_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())),
      N::n::ctor::Npos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))));

  static inline const std::shared_ptr<Z::z> z_zero = Z::z::ctor::Z0_();

  static inline const std::shared_ptr<Z::z> z_pos =
      Z::z::ctor::Zpos_(Positive::positive::ctor::xO_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
              Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
                  Positive::positive::ctor::xH_()))))));

  static inline const std::shared_ptr<Z::z> z_neg =
      Z::z::ctor::Zneg_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<Z::z> z_add_result = Z::add(
      Z::z::ctor::Zpos_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xI_(
              Positive::positive::ctor::xO_(Positive::positive::ctor::xH_())))),
      Z::z::ctor::Zneg_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<Z::z> z_mul_result = Z::mul(
      Z::z::ctor::Zneg_(Positive::positive::ctor::xO_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))),
      Z::z::ctor::Zpos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))));

  static inline const std::shared_ptr<Z::z> z_sub_result =
      Z::sub(Z::z::ctor::Zpos_(Positive::positive::ctor::xI_(
                 Positive::positive::ctor::xH_())),
             Z::z::ctor::Zpos_(Positive::positive::ctor::xO_(
                 Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
                     Positive::positive::ctor::xH_())))));

  static inline const std::shared_ptr<Z::z> z_abs_result =
      Z::abs(Z::z::ctor::Zneg_(Positive::positive::ctor::xO_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
              Positive::positive::ctor::xI_(Positive::positive::ctor::xO_(
                  Positive::positive::ctor::xH_())))))));

  static inline const comparison z_compare_result = Z::compare(
      Z::z::ctor::Zneg_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())),
      Z::z::ctor::Zpos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))));

  static inline const unsigned int pos_to_nat =
      Coq_Pos::to_nat(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())));

  static inline const unsigned int n_to_nat = N::to_nat(N::n::ctor::Npos_(
      Positive::positive::ctor::xI_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())))));

  static inline const unsigned int z_to_nat = Z::to_nat(Z::z::ctor::Zpos_(
      Positive::positive::ctor::xO_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_())))));

  static std::shared_ptr<N::n> n_max(std::shared_ptr<N::n> a,
                                     std::shared_ptr<N::n> b);

  static std::shared_ptr<Z::z> z_sign(const std::shared_ptr<Z::z> &z);

  static inline const std::shared_ptr<N::n> test_n_max = n_max(
      N::n::ctor::Npos_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())),
      N::n::ctor::Npos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_()))));

  static inline const std::shared_ptr<Z::z> test_z_sign_pos =
      z_sign(Z::z::ctor::Zpos_(Positive::positive::ctor::xI_(
          Positive::positive::ctor::xO_(Positive::positive::ctor::xH_()))));

  static inline const std::shared_ptr<Z::z> test_z_sign_neg =
      z_sign(Z::z::ctor::Zneg_(
          Positive::positive::ctor::xI_(Positive::positive::ctor::xH_())));

  static inline const std::shared_ptr<Z::z> test_z_sign_zero =
      z_sign(Z::z::ctor::Z0_());
};
