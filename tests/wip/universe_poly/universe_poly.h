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

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<List::list<A>> nil_uptr() {
        return std::unique_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::unique_ptr<List::list<A>>
      cons_uptr(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::unique_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

template <typename T1> T1 poly_id(const T1 x) { return x; }

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

template <typename A, typename B> struct ppair {
  A pfst;
  B psnd;
};

const std::shared_ptr<ppair<unsigned int, bool>> test_pair =
    std::make_shared<ppair<unsigned int, bool>>(
        ppair<unsigned int, bool>{(((((0 + 1) + 1) + 1) + 1) + 1), true});

const unsigned int test_pfst = test_pair->pfst;

const bool test_psnd = test_pair->psnd;

template <typename T1>
unsigned int poly_length(const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(
      Overloaded{[](const typename List::list<T1>::nil _args) -> unsigned int {
                   return 0;
                 },
                 [](const typename List::list<T1>::cons _args) -> unsigned int {
                   std::shared_ptr<List::list<T1>> rest = _args._a1;
                   return (poly_length<T1>(std::move(rest)) + 1);
                 }},
      l->v());
}

const unsigned int test_length =
    poly_length<unsigned int>(List::list<unsigned int>::ctor::cons_(
        (0 + 1),
        List::list<unsigned int>::ctor::cons_(
            ((0 + 1) + 1),
            List::list<unsigned int>::ctor::cons_(
                (((0 + 1) + 1) + 1), List::list<unsigned int>::ctor::nil_()))));
