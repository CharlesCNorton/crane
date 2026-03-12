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

template <typename M>
concept Container = requires {
  typename M::t;
  typename M::inner;
  typename M::elem;
};
template <typename M>
concept NestedContainer = requires {
  typename M::outer;
  typename M::middle;
  typename M::inner;
};

struct DependentTemplateStress {
  template <Container C> struct UseContainer {
    static const typename C::t<unsigned int> &make_nat_container() {
      static const typename C::t<unsigned int> v = C::empty<unsigned int>;
      return v;
    }

    static const typename C::inner<unsigned int> &make_inner_nat() {
      static const typename C::inner<unsigned int> v =
          C::wrap<unsigned int>(0u);
      return v;
    }

    static const typename C::t<bool> &make_bool_container() {
      static const typename C::t<bool> v = C::empty<bool>;
      return v;
    }

    static const typename C::t<unsigned int> &use_both() {
      static const typename C::t<unsigned int> v =
          C::singleton<unsigned int>(42u);
      return v;
    }

    static typename C::t<unsigned int> complex_use(const unsigned int _x0) {
      return C::singleton<unsigned int>(_x0);
    }
  };

  template <NestedContainer N> struct UseNested {
    static const typename N::outer<unsigned int> &make_outer_nat() {
      static const typename N::outer<unsigned int> v =
          N::mk_outer<unsigned int>(
              N::mk_middle<unsigned int>(N::mk_inner<unsigned int>(0u)));
      return v;
    }

    static const typename N::middle<bool> &make_middle_bool() {
      static const typename N::middle<bool> v =
          N::mk_middle<bool>(N::mk_inner<bool>(true));
      return v;
    }

    static const typename N::outer<unsigned int> &get_outer() {
      static const typename N::outer<unsigned int> v = make_outer_nat();
      return v;
    }
  };

  template <Container C1, Container C2> struct Compose {
    static const typename C1::t<unsigned int> &use_c1() {
      static const typename C1::t<unsigned int> v = C1::empty<unsigned int>;
      return v;
    }

    static const typename C2::t<bool> &use_c2() {
      static const typename C2::t<bool> v = C2::empty<bool>;
      return v;
    }

    static const typename C1::inner<unsigned int> &use_c1_inner() {
      static const typename C1::inner<unsigned int> v =
          C1::wrap<unsigned int>(0u);
      return v;
    }

    static const typename C2::inner<bool> &use_c2_inner() {
      static const typename C2::inner<bool> v = C2::wrap<bool>(true);
      return v;
    }
  };
};
