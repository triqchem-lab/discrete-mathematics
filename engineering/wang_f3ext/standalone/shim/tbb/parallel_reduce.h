#pragma once
#include <tbb/blocked_range.h>
namespace tbb {
template <class Range, class Init, class Func, class Comb>
Init parallel_reduce(const Range &r, Init init, Func f, Comb) {
  return f(r, init);
}
}
