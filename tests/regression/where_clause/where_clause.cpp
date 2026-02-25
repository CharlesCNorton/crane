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
#include <where_clause.h>

unsigned int WhereClause::eval(const std::shared_ptr<WhereClause::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::expr::Num _args) -> unsigned int {
            unsigned int n = _args._a0;
            return std::move(n);
          },
          [](const typename WhereClause::expr::Plus _args) -> unsigned int {
            std::shared_ptr<WhereClause::expr> a = _args._a0;
            std::shared_ptr<WhereClause::expr> b = _args._a1;
            return (eval(std::move(a)) + eval(std::move(b)));
          },
          [](const typename WhereClause::expr::Times _args) -> unsigned int {
            std::shared_ptr<WhereClause::expr> a = _args._a0;
            std::shared_ptr<WhereClause::expr> b = _args._a1;
            return (eval(std::move(a)) * eval(std::move(b)));
          }},
      e->v());
}

unsigned int
WhereClause::expr_size(const std::shared_ptr<WhereClause::expr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::expr::Num _args) -> unsigned int {
            return (0 + 1);
          },
          [](const typename WhereClause::expr::Plus _args) -> unsigned int {
            std::shared_ptr<WhereClause::expr> a = _args._a0;
            std::shared_ptr<WhereClause::expr> b = _args._a1;
            return (((0 + 1) + expr_size(std::move(a))) +
                    expr_size(std::move(b)));
          },
          [](const typename WhereClause::expr::Times _args) -> unsigned int {
            std::shared_ptr<WhereClause::expr> a = _args._a0;
            std::shared_ptr<WhereClause::expr> b = _args._a1;
            return (((0 + 1) + expr_size(std::move(a))) +
                    expr_size(std::move(b)));
          }},
      e->v());
}

bool WhereClause::beval(const std::shared_ptr<WhereClause::bExpr> &e) {
  return std::visit(
      Overloaded{[](const typename WhereClause::bExpr::BTrue _args) -> bool {
                   return true;
                 },
                 [](const typename WhereClause::bExpr::BFalse _args) -> bool {
                   return false;
                 },
                 [](const typename WhereClause::bExpr::BAnd _args) -> bool {
                   std::shared_ptr<WhereClause::bExpr> a = _args._a0;
                   std::shared_ptr<WhereClause::bExpr> b = _args._a1;
                   return (beval(std::move(a)) && beval(std::move(b)));
                 },
                 [](const typename WhereClause::bExpr::BOr _args) -> bool {
                   std::shared_ptr<WhereClause::bExpr> a = _args._a0;
                   std::shared_ptr<WhereClause::bExpr> b = _args._a1;
                   return (beval(std::move(a)) || beval(std::move(b)));
                 },
                 [](const typename WhereClause::bExpr::BNot _args) -> bool {
                   std::shared_ptr<WhereClause::bExpr> a = _args._a0;
                   return !(beval(std::move(a)));
                 }},
      e->v());
}

unsigned int WhereClause::aeval(const std::shared_ptr<WhereClause::aExpr> &e) {
  return std::visit(
      Overloaded{
          [](const typename WhereClause::aExpr::ANum _args) -> unsigned int {
            unsigned int n = _args._a0;
            return std::move(n);
          },
          [](const typename WhereClause::aExpr::APlus _args) -> unsigned int {
            std::shared_ptr<WhereClause::aExpr> a = _args._a0;
            std::shared_ptr<WhereClause::aExpr> b = _args._a1;
            return (aeval(std::move(a)) + aeval(std::move(b)));
          },
          [](const typename WhereClause::aExpr::AIf _args) -> unsigned int {
            std::shared_ptr<WhereClause::bExpr> c = _args._a0;
            std::shared_ptr<WhereClause::aExpr> t = _args._a1;
            std::shared_ptr<WhereClause::aExpr> f = _args._a2;
            if (beval(c)) {
              return aeval(std::move(t));
            } else {
              return aeval(std::move(f));
            }
          }},
      e->v());
}
