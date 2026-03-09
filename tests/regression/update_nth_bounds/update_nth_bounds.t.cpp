// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>
#include <update_nth_bounds.h>
int main() {
  // In-bounds update preserves length
  assert(UpdateNthBounds::in_bounds_length == 4u);
  // Out-of-bounds update preserves length
  assert(UpdateNthBounds::out_of_bounds_length == 3u);
  return 0;
}
