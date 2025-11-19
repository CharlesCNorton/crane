#include <algorithm>
#include <functional>
#include <future>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

namespace partest {
unsigned int ack(const std::pair<unsigned int, unsigned int> p);

std::pair<unsigned int, unsigned int> fast(const unsigned int m,
                                           const unsigned int n);

std::pair<unsigned int, unsigned int> slow(const unsigned int m,
                                           const unsigned int n);

}; // namespace partest
