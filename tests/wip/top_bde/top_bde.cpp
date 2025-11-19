#include <bdlf_overloaded.h>
#include <bsl_algorithm.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <top_bde.h>

namespace BloombergLP {

}
namespace list {

};

bsl::shared_ptr<list::list<unsigned int> > seq(const unsigned int start,
                                               const unsigned int len)
{
    if (len <= 0) {
        return list::nil<unsigned int>::make();
    }
    else {
        unsigned int len0 = len - 1;
        return list::cons<unsigned int>::make(start, seq((start + 1), len0));
    }
}
