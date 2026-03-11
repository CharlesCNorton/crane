// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <get_pair_bound_prop.h>

#include <cassert>

int main() {
  auto val = GetPairBoundProp::get_pair(GetPairBoundProp::sample, 10u);
  assert(val < 256u);
  return 0;
}
