#pragma once
#include <tbb/blocked_range.h>
namespace tbb {
template <class T, class Func> void parallel_for(T b, T e, Func f) {
  for (T i = b; i < e; ++i) f(i);
}
}
