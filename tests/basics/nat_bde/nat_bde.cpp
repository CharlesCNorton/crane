#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <nat_bde.h>

namespace BloombergLP {

}
namespace Nat {
namespace nat {
bsl::shared_ptr<nat> O::make()
{
    return bsl::make_shared<nat>(O{});
}
bsl::shared_ptr<nat> S::make(bsl::shared_ptr<nat> _a0)
{
    return bsl::make_shared<nat>(S{_a0});
}
};

bsl::shared_ptr<nat::nat> add(const bsl::shared_ptr<nat::nat> m,
                              const bsl::shared_ptr<nat::nat> n)
{
    return bsl::visit(
        bdlf::Overloaded{[&](const nat::O _args) -> bsl::shared_ptr<nat::nat> {
                             return n;
                         },
                         [&](const nat::S _args) -> bsl::shared_ptr<nat::nat> {
                             bsl::shared_ptr<nat::nat> x = _args._a0;
                             return nat::S::make(add(x, n));
                         }},
        *m);
}

int nat_to_int(const bsl::shared_ptr<nat::nat> n)
{
    return bsl::visit(
                 bdlf::Overloaded{[&](const nat::O _args) -> int {
                                      return 0;
                                  },
                                  [&](const nat::S _args) -> int {
                                      bsl::shared_ptr<nat::nat> n_ = _args._a0;
                                      return 1 + nat_to_int(n_);
                                  }},
                 *n);
}

};
