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
    unsigned int length() const {
      return std::visit(
          Overloaded{
              [](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (std::move(l_)->length() + 1);
              }},
          this->v());
    }
  };
};

unsigned int
deep_option(const std::optional<std::optional<std::optional<unsigned int>>> x);

unsigned int deep_pair(const std::pair<std::pair<unsigned int, unsigned int>,
                                       std::pair<unsigned int, unsigned int>>
                           p);

unsigned int list_shape(const std::shared_ptr<List::list<unsigned int>> &l);

struct outer;
struct inner;
struct Outer {
  struct outer {
  public:
    struct OLeft {
      std::shared_ptr<Inner::inner> _a0;
    };
    struct ORight {
      unsigned int _a0;
    };
    using variant_t = std::variant<OLeft, ORight>;

  private:
    variant_t v_;
    explicit outer(OLeft _v) : v_(std::move(_v)) {}
    explicit outer(ORight _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Outer::outer>
      OLeft_(const std::shared_ptr<Inner::inner> &a0) {
        return std::shared_ptr<Outer::outer>(new Outer::outer(OLeft{a0}));
      }
      static std::shared_ptr<Outer::outer> ORight_(unsigned int a0) {
        return std::shared_ptr<Outer::outer>(new Outer::outer(ORight{a0}));
      }
      static std::unique_ptr<Outer::outer>
      OLeft_uptr(const std::shared_ptr<Inner::inner> &a0) {
        return std::unique_ptr<Outer::outer>(new Outer::outer(OLeft{a0}));
      }
      static std::unique_ptr<Outer::outer> ORight_uptr(unsigned int a0) {
        return std::unique_ptr<Outer::outer>(new Outer::outer(ORight{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
    unsigned int deep_sum() const {
      return std::visit(
          Overloaded{
              [](const typename Outer::outer::OLeft _args) -> unsigned int {
                std::shared_ptr<Inner::inner> i = _args._a0;
                return std::visit(
                    Overloaded{[](const typename Inner::inner::ILeft _args)
                                   -> unsigned int {
                                 unsigned int n = _args._a0;
                                 return std::move(n);
                               },
                               [](const typename Inner::inner::IRight _args)
                                   -> unsigned int {
                                 bool b = _args._a0;
                                 if (b) {
                                   return (0 + 1);
                                 } else {
                                   return 0;
                                 }
                               }},
                    std::move(i)->v());
              },
              [](const typename Outer::outer::ORight _args) -> unsigned int {
                unsigned int n = _args._a0;
return (std::move(n) + ((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
              }},
          this->v());
    }
  };
};
struct Inner {
  struct inner {
  public:
    struct ILeft {
      unsigned int _a0;
    };
    struct IRight {
      bool _a0;
    };
    using variant_t = std::variant<ILeft, IRight>;

  private:
    variant_t v_;
    explicit inner(ILeft _v) : v_(std::move(_v)) {}
    explicit inner(IRight _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Inner::inner> ILeft_(unsigned int a0) {
        return std::shared_ptr<Inner::inner>(new Inner::inner(ILeft{a0}));
      }
      static std::shared_ptr<Inner::inner> IRight_(bool a0) {
        return std::shared_ptr<Inner::inner>(new Inner::inner(IRight{a0}));
      }
      static std::unique_ptr<Inner::inner> ILeft_uptr(unsigned int a0) {
        return std::unique_ptr<Inner::inner>(new Inner::inner(ILeft{a0}));
      }
      static std::unique_ptr<Inner::inner> IRight_uptr(bool a0) {
        return std::unique_ptr<Inner::inner>(new Inner::inner(IRight{a0}));
      }
    };
    const variant_t &v() const { return v_; }
    variant_t &v_mut() { return v_; }
  };
};

unsigned int complex_match(
    const std::optional<
        std::pair<unsigned int, std::shared_ptr<List::list<unsigned int>>>>
        x);

unsigned int guarded_match(const std::pair<unsigned int, unsigned int> p);

const unsigned int test_deep_some =
    deep_option(std::make_optional<std::optional<std::optional<unsigned int>>>(
        std::make_optional<std::optional<unsigned int>>(
            std::make_optional<unsigned int>((
                (((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) +
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
                 1) +
                1)))));

const unsigned int test_deep_none =
    deep_option(std::make_optional<std::optional<std::optional<unsigned int>>>(
        std::make_optional<std::optional<unsigned int>>(std::nullopt)));

const unsigned int test_deep_pair = deep_pair(std::make_pair(
    std::make_pair((0 + 1), ((0 + 1) + 1)),
    std::make_pair((((0 + 1) + 1) + 1), ((((0 + 1) + 1) + 1) + 1))));

const unsigned int test_shape_3 =
    list_shape(List::list<unsigned int>::ctor::cons_(
        ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
        List::list<unsigned int>::ctor::cons_(
            ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
             1),
            List::list<unsigned int>::ctor::cons_(
                ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) +
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
                 1),
                List::list<unsigned int>::ctor::nil_()))));

const unsigned int test_shape_long =
    list_shape(List::list<unsigned int>::ctor::cons_(
        (0 + 1),
        List::list<unsigned int>::ctor::cons_(
            ((0 + 1) + 1),
            List::list<unsigned int>::ctor::cons_(
                (((0 + 1) + 1) + 1),
                List::list<unsigned int>::ctor::cons_(
                    ((((0 + 1) + 1) + 1) + 1),
                    List::list<unsigned int>::ctor::cons_(
                        (((((0 + 1) + 1) + 1) + 1) + 1),
                        List::list<unsigned int>::ctor::cons_(
                            ((((((0 + 1) + 1) + 1) + 1) + 1) + 1),
                            List::list<unsigned int>::ctor::nil_())))))));

const unsigned int test_deep_sum = Outer::outer::ctor::OLeft_(Inner::inner::ctor::ILeft_((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)))->deep_sum();

const unsigned int test_complex = complex_match(
    std::make_optional<
        std::pair<unsigned int, std::shared_ptr<List::list<unsigned int>>>>(
        std::make_pair(
            (((((0 + 1) + 1) + 1) + 1) + 1),
            List::list<unsigned int>::ctor::cons_(
                ((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1),
                List::list<unsigned int>::ctor::cons_(
                    ((((((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
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
                     1),
                    List::list<unsigned int>::ctor::cons_(
                        ((((((((((((((((((((((((((((((0 + 1) + 1) + 1) + 1) +
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
                         1),
                        List::list<unsigned int>::ctor::nil_()))))));

const unsigned int test_guarded = guarded_match(std::make_pair(
    (((0 + 1) + 1) + 1), (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1)));
