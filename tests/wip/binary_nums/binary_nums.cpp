#include <algorithm>
#include <any>
#include <binary_nums.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Positive::positive>
Pos::succ(const std::shared_ptr<Positive::positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::positive::xI _args)
                     -> std::shared_ptr<Positive::positive> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Positive::positive::ctor::xO_(succ(std::move(p)));
                 },
                 [](const typename Positive::positive::xO _args)
                     -> std::shared_ptr<Positive::positive> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Positive::positive::ctor::xI_(std::move(p));
                 },
                 [](const typename Positive::positive::xH _args)
                     -> std::shared_ptr<Positive::positive> {
                   return Positive::positive::ctor::xO_(
                       Positive::positive::ctor::xH_());
                 }},
      x->v());
}

std::shared_ptr<Positive::positive>
Pos::add(const std::shared_ptr<Positive::positive> &x,
         const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xO_(
                                 succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xI_(std::move(p));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Positive::positive> {
            return std::visit(
                Overloaded{[](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 succ(std::move(q)));
                           },
                           [](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(std::move(q));
                           },
                           [](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xO_(
                                 Positive::positive::ctor::xH_());
                           }},
                y->v());
          }},
      x->v());
}
std::shared_ptr<Positive::positive>
Pos::add_carry(const std::shared_ptr<Positive::positive> &x,
               const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xI_(
                                 succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xO_(
                                 succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Positive::positive> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::positive::xI _args)
                        -> std::shared_ptr<Positive::positive> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return Positive::positive::ctor::xI_(succ(std::move(q)));
                    },
                    [](const typename Positive::positive::xO _args)
                        -> std::shared_ptr<Positive::positive> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return Positive::positive::ctor::xO_(succ(std::move(q)));
                    },
                    [](const typename Positive::positive::xH _args)
                        -> std::shared_ptr<Positive::positive> {
                      return Positive::positive::ctor::xI_(
                          Positive::positive::ctor::xH_());
                    }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive::positive>
Pos::pred_double(const std::shared_ptr<Positive::positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::positive::xI _args)
                     -> std::shared_ptr<Positive::positive> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Positive::positive::ctor::xI_(
                       Positive::positive::ctor::xO_(std::move(p)));
                 },
                 [](const typename Positive::positive::xO _args)
                     -> std::shared_ptr<Positive::positive> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Positive::positive::ctor::xI_(
                       pred_double(std::move(p)));
                 },
                 [](const typename Positive::positive::xH _args)
                     -> std::shared_ptr<Positive::positive> {
                   return Positive::positive::ctor::xH_();
                 }},
      x->v());
}

std::shared_ptr<N::n>
Pos::pred_N(const std::shared_ptr<Positive::positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::positive::xI _args)
                     -> std::shared_ptr<N::n> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return N::n::ctor::Npos_(
                       Positive::positive::ctor::xO_(std::move(p)));
                 },
                 [](const typename Positive::positive::xO _args)
                     -> std::shared_ptr<N::n> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return N::n::ctor::Npos_(pred_double(std::move(p)));
                 },
                 [](const typename Positive::positive::xH _args)
                     -> std::shared_ptr<N::n> { return N::n::ctor::N0_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::succ_double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{
          [](const typename Pos::mask::IsNul _args)
              -> std::shared_ptr<Pos::mask> {
            return mask::ctor::IsPos_(Positive::positive::ctor::xH_());
          },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return mask::ctor::IsPos_(
                Positive::positive::ctor::xI_(std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_mask(const std::shared_ptr<Pos::mask> &x) {
  return std::visit(
      Overloaded{
          [](const typename Pos::mask::IsNul _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNul_(); },
          [](const typename Pos::mask::IsPos _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return mask::ctor::IsPos_(
                Positive::positive::ctor::xO_(std::move(p)));
          },
          [](const typename Pos::mask::IsNeg _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::double_pred_mask(const std::shared_ptr<Positive::positive> &x) {
  return std::visit(
      Overloaded{
          [](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return mask::ctor::IsPos_(Positive::positive::ctor::xO_(
                Positive::positive::ctor::xO_(std::move(p))));
          },
          [](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return mask::ctor::IsPos_(
                Positive::positive::ctor::xO_(pred_double(std::move(p))));
          },
          [](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNul_(); }},
      x->v());
}

std::shared_ptr<Pos::mask>
Pos::sub_mask(const std::shared_ptr<Positive::positive> &x,
              const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return double_mask(
                                 sub_mask(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return succ_double_mask(
                                 sub_mask(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ctor::IsPos_(
                                 Positive::positive::ctor::xO_(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::positive::xI _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return succ_double_mask(
                          sub_mask_carry(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::positive::xO _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return double_mask(sub_mask(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::positive::xH _args)
                        -> std::shared_ptr<Pos::mask> {
                      return mask::ctor::IsPos_(pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Pos::mask> {
            return std::visit(
                Overloaded{[](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ctor::IsNeg_();
                           },
                           [](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ctor::IsNeg_();
                           },
                           [](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return mask::ctor::IsNul_();
                           }},
                y->v());
          }},
      x->v());
}
std::shared_ptr<Pos::mask>
Pos::sub_mask_carry(const std::shared_ptr<Positive::positive> &x,
                    const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::positive::xI _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return succ_double_mask(
                          sub_mask_carry(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::positive::xO _args)
                        -> std::shared_ptr<Pos::mask> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return double_mask(sub_mask(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::positive::xH _args)
                        -> std::shared_ptr<Pos::mask> {
                      return mask::ctor::IsPos_(pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Pos::mask> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return double_mask(
                                 sub_mask_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Pos::mask> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return succ_double_mask(
                                 sub_mask_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Pos::mask> {
                             return double_pred_mask(std::move(p));
                           }},
                y->v());
          },
          [](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Pos::mask> { return mask::ctor::IsNeg_(); }},
      x->v());
}

std::shared_ptr<Positive::positive>
Pos::mul(const std::shared_ptr<Positive::positive> &x,
         std::shared_ptr<Positive::positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return add(y, Positive::positive::ctor::xO_(mul(std::move(p), y)));
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return Positive::positive::ctor::xO_(
                mul(std::move(p), std::move(y)));
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Positive::positive> { return std::move(y); }},
      x->v());
}

comparison Pos::compare_cont(const comparison r,
                             const std::shared_ptr<Positive::positive> &x,
                             const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args) -> comparison {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> comparison {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return compare_cont(r, std::move(p), std::move(q));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> comparison {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return compare_cont(comparison::Gt, std::move(p),
                                                 std::move(q));
                           },
                           [](const typename Positive::positive::xH _args)
                               -> comparison { return comparison::Gt; }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args) -> comparison {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> comparison {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return compare_cont(comparison::Lt, std::move(p),
                                                 std::move(q));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> comparison {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return compare_cont(r, std::move(p), std::move(q));
                           },
                           [](const typename Positive::positive::xH _args)
                               -> comparison { return comparison::Gt; }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args) -> comparison {
            return std::visit(
                Overloaded{[](const typename Positive::positive::xI _args)
                               -> comparison { return comparison::Lt; },
                           [](const typename Positive::positive::xO _args)
                               -> comparison { return comparison::Lt; },
                           [&](const typename Positive::positive::xH _args)
                               -> comparison { return r; }},
                y->v());
          }},
      x->v());
}

comparison Pos::compare(const std::shared_ptr<Positive::positive> &_x0,
                        const std::shared_ptr<Positive::positive> &_x1) {
  return [](const std::shared_ptr<Positive::positive> _x0,
            const std::shared_ptr<Positive::positive> _x1) {
    return compare_cont(comparison::Eq, _x0, _x1);
  }(_x0, _x1);
}

unsigned int Pos::to_nat(const std::shared_ptr<Positive::positive> &x) {
  return iter_op<unsigned int>(
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      },
      x, (0 + 1));
}

std::shared_ptr<Positive::positive>
Coq_Pos::succ(const std::shared_ptr<Positive::positive> &x) {
  return std::visit(
      Overloaded{[](const typename Positive::positive::xI _args)
                     -> std::shared_ptr<Positive::positive> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Positive::positive::ctor::xO_(::succ(std::move(p)));
                 },
                 [](const typename Positive::positive::xO _args)
                     -> std::shared_ptr<Positive::positive> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Positive::positive::ctor::xI_(std::move(p));
                 },
                 [](const typename Positive::positive::xH _args)
                     -> std::shared_ptr<Positive::positive> {
                   return Positive::positive::ctor::xO_(
                       Positive::positive::ctor::xH_());
                 }},
      x->v());
}

std::shared_ptr<Positive::positive>
Coq_Pos::add(const std::shared_ptr<Positive::positive> &x,
             const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 ::add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 ::add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xO_(
                                 ::succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 ::add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 ::add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xI_(std::move(p));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Positive::positive> {
            return std::visit(
                Overloaded{[](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 ::succ(std::move(q)));
                           },
                           [](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(std::move(q));
                           },
                           [](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xO_(
                                 Positive::positive::ctor::xH_());
                           }},
                y->v());
          }},
      x->v());
}
std::shared_ptr<Positive::positive>
Coq_Pos::add_carry(const std::shared_ptr<Positive::positive> &x,
                   const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 ::add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 ::add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xI_(
                                 ::succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 ::add_carry(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 ::add(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xO_(
                                 ::succ(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Positive::positive> {
            return std::visit(
                Overloaded{[](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xI_(
                                 ::succ(std::move(q)));
                           },
                           [](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Positive::positive> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return Positive::positive::ctor::xO_(
                                 ::succ(std::move(q)));
                           },
                           [](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Positive::positive> {
                             return Positive::positive::ctor::xI_(
                                 Positive::positive::ctor::xH_());
                           }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Positive::positive>
Coq_Pos::mul(const std::shared_ptr<Positive::positive> &x,
             std::shared_ptr<Positive::positive> y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return ::add(y,
                         Positive::positive::ctor::xO_(::mul(std::move(p), y)));
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Positive::positive> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return Positive::positive::ctor::xO_(
                ::mul(std::move(p), std::move(y)));
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Positive::positive> { return std::move(y); }},
      x->v());
}

unsigned int Coq_Pos::to_nat(const std::shared_ptr<Positive::positive> &x) {
  return ::iter_op<unsigned int>(
      [](const unsigned int _x0, const unsigned int _x1) {
        return (_x0 + _x1);
      },
      x, (0 + 1));
}

std::shared_ptr<N::n> N::sub(std::shared_ptr<N::n> n,
                             const std::shared_ptr<N::n> &m) {
  return [&](void) {
    if (n.use_count() == 1 && n->v().index() == 0) {
      auto &_rf = std::get<0>(n->v_mut());
      return n;
    } else {
      return std::visit(
          Overloaded{
              [](const typename N::n::N0 _args) -> std::shared_ptr<N::n> {
                return N::n::ctor::N0_();
              },
              [&](const typename N::n::Npos _args) -> std::shared_ptr<N::n> {
                std::shared_ptr<Positive::positive> n_ = _args._a0;
                return std::visit(
                    Overloaded{
                        [&](const typename N::n::N0 _args)
                            -> std::shared_ptr<N::n> { return std::move(n); },
                        [&](const typename N::n::Npos _args)
                            -> std::shared_ptr<N::n> {
                          std::shared_ptr<Positive::positive> m_ = _args._a0;
                          return std::visit(
                              Overloaded{
                                  [](const typename Pos::mask::IsNul _args)
                                      -> std::shared_ptr<N::n> {
                                    return N::n::ctor::N0_();
                                  },
                                  [](const typename Pos::mask::IsPos _args)
                                      -> std::shared_ptr<N::n> {
                                    std::shared_ptr<Positive::positive> p =
                                        _args._a0;
                                    return N::n::ctor::Npos_(std::move(p));
                                  },
                                  [](const typename Pos::mask::IsNeg _args)
                                      -> std::shared_ptr<N::n> {
                                    return N::n::ctor::N0_();
                                  }},
                              Pos::sub_mask(std::move(n_), std::move(m_))->v());
                        }},
                    m->v());
              }},
          n->v());
    }
  }();
}

comparison N::compare(const std::shared_ptr<N::n> &n,
                      const std::shared_ptr<N::n> &m) {
  return std::visit(
      Overloaded{
          [&](const typename N::n::N0 _args) -> comparison {
            return std::visit(
                Overloaded{[](const typename N::n::N0 _args) -> comparison {
                             return comparison::Eq;
                           },
                           [](const typename N::n::Npos _args) -> comparison {
                             return comparison::Lt;
                           }},
                m->v());
          },
          [&](const typename N::n::Npos _args) -> comparison {
            std::shared_ptr<Positive::positive> n_ = _args._a0;
            return std::visit(
                Overloaded{[](const typename N::n::N0 _args) -> comparison {
                             return comparison::Gt;
                           },
                           [&](const typename N::n::Npos _args) -> comparison {
                             std::shared_ptr<Positive::positive> m_ = _args._a0;
                             return Pos::compare(std::move(n_), std::move(m_));
                           }},
                m->v());
          }},
      n->v());
}

std::shared_ptr<N::n> N::pred(const std::shared_ptr<N::n> &n) {
  return std::visit(
      Overloaded{[](const typename N::n::N0 _args) -> std::shared_ptr<N::n> {
                   return N::n::ctor::N0_();
                 },
                 [](const typename N::n::Npos _args) -> std::shared_ptr<N::n> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Pos::pred_N(std::move(p));
                 }},
      n->v());
}

std::shared_ptr<N::n> N::add(std::shared_ptr<N::n> n, std::shared_ptr<N::n> m) {
  return std::visit(
      Overloaded{
          [&](const typename N::n::N0 _args) -> std::shared_ptr<N::n> {
            return std::move(m);
          },
          [&](const typename N::n::Npos _args) -> std::shared_ptr<N::n> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return [&](void) {
              if (std::move(m).use_count() == 1 &&
                  std::move(m)->v().index() == 1) {
                auto &_rf = std::get<1>(std::move(m)->v_mut());
                std::shared_ptr<Positive::positive> q = std::move(_rf._a0);
                _rf._a0 = Coq_Pos::add(std::move(p), std::move(q));
                return std::move(m);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename N::n::N0 _args)
                            -> std::shared_ptr<N::n> { return std::move(n); },
                        [&](const typename N::n::Npos _args)
                            -> std::shared_ptr<N::n> {
                          std::shared_ptr<Positive::positive> q = _args._a0;
                          return N::n::ctor::Npos_(
                              Coq_Pos::add(std::move(p), std::move(q)));
                        }},
                    std::move(m)->v());
              }
            }();
          }},
      n->v());
}

std::shared_ptr<N::n> N::mul(const std::shared_ptr<N::n> &n,
                             const std::shared_ptr<N::n> &m) {
  return std::visit(
      Overloaded{
          [](const typename N::n::N0 _args) -> std::shared_ptr<N::n> {
            return N::n::ctor::N0_();
          },
          [&](const typename N::n::Npos _args) -> std::shared_ptr<N::n> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename N::n::N0 _args) -> std::shared_ptr<N::n> {
                      return N::n::ctor::N0_();
                    },
                    [&](const typename N::n::Npos _args)
                        -> std::shared_ptr<N::n> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return N::n::ctor::Npos_(
                          Coq_Pos::mul(std::move(p), std::move(q)));
                    }},
                m->v());
          }},
      n->v());
}

unsigned int N::to_nat(const std::shared_ptr<N::n> &a) {
  return std::visit(
      Overloaded{
          [](const typename N::n::N0 _args) -> unsigned int { return 0; },
          [](const typename N::n::Npos _args) -> unsigned int {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return Pos::to_nat(std::move(p));
          }},
      a->v());
}

std::shared_ptr<Z::z> Z::double(const std::shared_ptr<Z::z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Z0_();
                 },
                 [](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zpos_(
                       Positive::positive::ctor::xO_(std::move(p)));
                 },
                 [](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zneg_(
                       Positive::positive::ctor::xO_(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z::z> Z::succ_double(const std::shared_ptr<Z::z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Zpos_(Positive::positive::ctor::xH_());
                 },
                 [](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zpos_(
                       Positive::positive::ctor::xI_(std::move(p)));
                 },
                 [](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zneg_(Pos::pred_double(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z::z> Z::pred_double(const std::shared_ptr<Z::z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Zneg_(Positive::positive::ctor::xH_());
                 },
                 [](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zpos_(Pos::pred_double(std::move(p)));
                 },
                 [](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zneg_(
                       Positive::positive::ctor::xI_(std::move(p)));
                 }},
      x->v());
}

std::shared_ptr<Z::z> Z::pos_sub(const std::shared_ptr<Positive::positive> &x,
                                 const std::shared_ptr<Positive::positive> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Positive::positive::xI _args)
              -> std::shared_ptr<Z::z> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{[&](const typename Positive::positive::xI _args)
                               -> std::shared_ptr<Z::z> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return double(pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xO _args)
                               -> std::shared_ptr<Z::z> {
                             std::shared_ptr<Positive::positive> q = _args._a0;
                             return succ_double(
                                 pos_sub(std::move(p), std::move(q)));
                           },
                           [&](const typename Positive::positive::xH _args)
                               -> std::shared_ptr<Z::z> {
                             return Z::z::ctor::Zpos_(
                                 Positive::positive::ctor::xO_(std::move(p)));
                           }},
                y->v());
          },
          [&](const typename Positive::positive::xO _args)
              -> std::shared_ptr<Z::z> {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return std::visit(
                Overloaded{
                    [&](const typename Positive::positive::xI _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return pred_double(pos_sub(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::positive::xO _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return double(pos_sub(std::move(p), std::move(q)));
                    },
                    [&](const typename Positive::positive::xH _args)
                        -> std::shared_ptr<Z::z> {
                      return Z::z::ctor::Zpos_(Pos::pred_double(std::move(p)));
                    }},
                y->v());
          },
          [&](const typename Positive::positive::xH _args)
              -> std::shared_ptr<Z::z> {
            return std::visit(
                Overloaded{
                    [](const typename Positive::positive::xI _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return Z::z::ctor::Zneg_(
                          Positive::positive::ctor::xO_(std::move(q)));
                    },
                    [](const typename Positive::positive::xO _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> q = _args._a0;
                      return Z::z::ctor::Zneg_(Pos::pred_double(std::move(q)));
                    },
                    [](const typename Positive::positive::xH _args)
                        -> std::shared_ptr<Z::z> { return Z::z::ctor::Z0_(); }},
                y->v());
          }},
      x->v());
}

std::shared_ptr<Z::z> Z::add(std::shared_ptr<Z::z> x, std::shared_ptr<Z::z> y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
            return std::move(y);
          },
          [&](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
            std::shared_ptr<Positive::positive> x_ = _args._a0;
            return [&](void) {
              if (std::move(y).use_count() == 1 &&
                  std::move(y)->v().index() == 1) {
                auto &_rf = std::get<1>(std::move(y)->v_mut());
                std::shared_ptr<Positive::positive> y_ = std::move(_rf._a0);
                _rf._a0 = Pos::add(std::move(x_), std::move(y_));
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::z::Z0 _args)
                            -> std::shared_ptr<Z::z> { return std::move(x); },
                        [&](const typename Z::z::Zpos _args)
                            -> std::shared_ptr<Z::z> {
                          std::shared_ptr<Positive::positive> y_ = _args._a0;
                          return Z::z::ctor::Zpos_(
                              Pos::add(std::move(x_), std::move(y_)));
                        },
                        [&](const typename Z::z::Zneg _args)
                            -> std::shared_ptr<Z::z> {
                          std::shared_ptr<Positive::positive> y_ = _args._a0;
                          return pos_sub(std::move(x_), std::move(y_));
                        }},
                    std::move(y)->v());
              }
            }();
          },
          [&](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
            std::shared_ptr<Positive::positive> x_ = _args._a0;
            return [&](void) {
              if (std::move(y).use_count() == 1 &&
                  std::move(y)->v().index() == 2) {
                auto &_rf = std::get<2>(std::move(y)->v_mut());
                std::shared_ptr<Positive::positive> y_ = std::move(_rf._a0);
                _rf._a0 = Pos::add(std::move(x_), std::move(y_));
                return std::move(y);
              } else {
                return std::visit(
                    Overloaded{
                        [&](const typename Z::z::Z0 _args)
                            -> std::shared_ptr<Z::z> { return std::move(x); },
                        [&](const typename Z::z::Zpos _args)
                            -> std::shared_ptr<Z::z> {
                          std::shared_ptr<Positive::positive> y_ = _args._a0;
                          return pos_sub(std::move(y_), std::move(x_));
                        },
                        [&](const typename Z::z::Zneg _args)
                            -> std::shared_ptr<Z::z> {
                          std::shared_ptr<Positive::positive> y_ = _args._a0;
                          return Z::z::ctor::Zneg_(
                              Pos::add(std::move(x_), std::move(y_)));
                        }},
                    std::move(y)->v());
              }
            }();
          }},
      x->v());
}

std::shared_ptr<Z::z> Z::opp(const std::shared_ptr<Z::z> &x) {
  return std::visit(
      Overloaded{[](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Z0_();
                 },
                 [](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> x0 = _args._a0;
                   return Z::z::ctor::Zneg_(std::move(x0));
                 },
                 [](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> x0 = _args._a0;
                   return Z::z::ctor::Zpos_(std::move(x0));
                 }},
      x->v());
}

std::shared_ptr<Z::z> Z::sub(const std::shared_ptr<Z::z> &m,
                             const std::shared_ptr<Z::z> &n) {
  return add(m, opp(n));
}

std::shared_ptr<Z::z> Z::mul(const std::shared_ptr<Z::z> &x,
                             const std::shared_ptr<Z::z> &y) {
  return std::visit(
      Overloaded{
          [](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
            return Z::z::ctor::Z0_();
          },
          [&](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
            std::shared_ptr<Positive::positive> x_ = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                      return Z::z::ctor::Z0_();
                    },
                    [&](const typename Z::z::Zpos _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> y_ = _args._a0;
                      return Z::z::ctor::Zpos_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    },
                    [&](const typename Z::z::Zneg _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> y_ = _args._a0;
                      return Z::z::ctor::Zneg_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    }},
                y->v());
          },
          [&](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
            std::shared_ptr<Positive::positive> x_ = _args._a0;
            return std::visit(
                Overloaded{
                    [](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                      return Z::z::ctor::Z0_();
                    },
                    [&](const typename Z::z::Zpos _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> y_ = _args._a0;
                      return Z::z::ctor::Zneg_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    },
                    [&](const typename Z::z::Zneg _args)
                        -> std::shared_ptr<Z::z> {
                      std::shared_ptr<Positive::positive> y_ = _args._a0;
                      return Z::z::ctor::Zpos_(
                          Pos::mul(std::move(x_), std::move(y_)));
                    }},
                y->v());
          }},
      x->v());
}

comparison Z::compare(const std::shared_ptr<Z::z> &x,
                      const std::shared_ptr<Z::z> &y) {
  return std::visit(
      Overloaded{
          [&](const typename Z::z::Z0 _args) -> comparison {
            return std::visit(
                Overloaded{[](const typename Z::z::Z0 _args) -> comparison {
                             return comparison::Eq;
                           },
                           [](const typename Z::z::Zpos _args) -> comparison {
                             return comparison::Lt;
                           },
                           [](const typename Z::z::Zneg _args) -> comparison {
                             return comparison::Gt;
                           }},
                y->v());
          },
          [&](const typename Z::z::Zpos _args) -> comparison {
            std::shared_ptr<Positive::positive> x_ = _args._a0;
            return std::visit(
                Overloaded{[](const typename Z::z::Z0 _args) -> comparison {
                             return comparison::Gt;
                           },
                           [&](const typename Z::z::Zpos _args) -> comparison {
                             std::shared_ptr<Positive::positive> y_ = _args._a0;
                             return Pos::compare(std::move(x_), std::move(y_));
                           },
                           [](const typename Z::z::Zneg _args) -> comparison {
                             return comparison::Gt;
                           }},
                y->v());
          },
          [&](const typename Z::z::Zneg _args) -> comparison {
            std::shared_ptr<Positive::positive> x_ = _args._a0;
            return std::visit(
                Overloaded{[](const typename Z::z::Z0 _args) -> comparison {
                             return comparison::Lt;
                           },
                           [](const typename Z::z::Zpos _args) -> comparison {
                             return comparison::Lt;
                           },
                           [&](const typename Z::z::Zneg _args) -> comparison {
                             std::shared_ptr<Positive::positive> y_ = _args._a0;
                             return Pos::compare(std::move(x_), std::move(y_))
                                 ->CompOpp();
                           }},
                y->v());
          }},
      x->v());
}

unsigned int Z::to_nat(const std::shared_ptr<Z::z> &z) {
  return std::visit(
      Overloaded{
          [](const typename Z::z::Z0 _args) -> unsigned int { return 0; },
          [](const typename Z::z::Zpos _args) -> unsigned int {
            std::shared_ptr<Positive::positive> p = _args._a0;
            return Pos::to_nat(std::move(p));
          },
          [](const typename Z::z::Zneg _args) -> unsigned int { return 0; }},
      z->v());
}

std::shared_ptr<Z::z> Z::abs(const std::shared_ptr<Z::z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Z0_();
                 },
                 [](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zpos_(std::move(p));
                 },
                 [](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
                   std::shared_ptr<Positive::positive> p = _args._a0;
                   return Z::z::ctor::Zpos_(std::move(p));
                 }},
      z->v());
}

std::shared_ptr<N::n> n_max(std::shared_ptr<N::n> a, std::shared_ptr<N::n> b) {
  return [&](void) {
    switch (N::compare(a, b)) {
    case comparison::Eq: {
      return std::move(a);
    }
    case comparison::Lt: {
      return std::move(b);
    }
    case comparison::Gt: {
      return std::move(a);
    }
    }
  }();
}

std::shared_ptr<Z::z> z_sign(const std::shared_ptr<Z::z> &z) {
  return std::visit(
      Overloaded{[](const typename Z::z::Z0 _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Z0_();
                 },
                 [](const typename Z::z::Zpos _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Zpos_(Positive::positive::ctor::xH_());
                 },
                 [](const typename Z::z::Zneg _args) -> std::shared_ptr<Z::z> {
                   return Z::z::ctor::Zneg_(Positive::positive::ctor::xH_());
                 }},
      z->v());
}
