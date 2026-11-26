#pragma once
// 区间终点一律钳到 last: 分块不整除且末块起点 >= last 时, 倒数第二块不得越过 last
// (2026-11-27 实测: n=13/8 线程时旧写法给出 [12,14) → 越界读 → F3 下界搜索 FATAL)。
// tbb 垫片(手工构建用): blocked_range / parallel_for / parallel_reduce 的 std::thread 实现。
// 语义与 oneTBB 对应重载一致(分块并行 + 可结合归约), 嵌套并行区域退化为串行(避免线程超额)。
#include <algorithm>
#include <cstddef>
#include <cstdlib>
#include <thread>
#include <type_traits>
#include <vector>

#include "tbb/blocked_range.h"

namespace tbb {
namespace shim {
inline unsigned MaxThreads() {
  static unsigned cached = [] {
    if (const char *e = std::getenv("SHIM_THREADS")) {
      int v = std::atoi(e);
      if (v > 0) return static_cast<unsigned>(v);
    }
    unsigned n = std::thread::hardware_concurrency();
    return n == 0 ? 1u : n;
  }();
  return cached;
}
// 嵌套并行区域计数(线程局部): >= 1 时内层并行调用直接串行执行。
inline int &Depth() {
  static thread_local int depth = 0;
  return depth;
}
struct DepthGuard {
  int &d;
  explicit DepthGuard(int &dd) : d(dd) { ++d; }
  ~DepthGuard() { --d; }
};
}  // namespace shim

// parallel_for(first, last, f): 对每个 i ∈ [first, last) 执行 f(i)。
template <class Index, class Func>
void parallel_for(Index first, Index last, const Func &f) {
  if (last <= first) return;
  if (shim::Depth() >= 1) {
    for (Index i = first; i < last; ++i) f(i);
    return;
  }
  shim::DepthGuard g(shim::Depth());
  const auto n = static_cast<std::make_unsigned_t<Index>>(last - first);
  unsigned nt = shim::MaxThreads();
  if (n < nt) nt = static_cast<unsigned>(n);
  if (nt <= 1) {
    for (Index i = first; i < last; ++i) f(i);
    return;
  }
  const auto chunk = static_cast<std::make_unsigned_t<Index>>((n + nt - 1) / nt);
  std::vector<std::thread> th;
  th.reserve(nt);
  for (unsigned t = 0; t < nt; ++t) {
    const auto off = static_cast<Index>(chunk * t);
    const Index b = first + off;
    if (b >= last) break;
    const Index e = std::min<Index>(last, static_cast<Index>(first + off + static_cast<Index>(chunk)));
    th.emplace_back([&f, b, e] {
      for (Index i = b; i < e; ++i) f(i);
    });
  }
  for (auto &x : th) x.join();
}

// parallel_for(range, f): 把 blocked_range 分块, 每块调用 f(blocked_range(块))。
template <class T, class Func>
void parallel_for(const blocked_range<T> &r, const Func &f) {
  const T first = r.begin();
  const T last = r.end();
  if (last <= first) return;
  if (shim::Depth() >= 1) {
    f(r);
    return;
  }
  shim::DepthGuard g(shim::Depth());
  const auto n = static_cast<std::make_unsigned_t<T>>(last - first);
  unsigned nt = shim::MaxThreads();
  if (n < nt) nt = static_cast<unsigned>(n);
  if (nt <= 1) {
    f(r);
    return;
  }
  const auto chunk = static_cast<std::make_unsigned_t<T>>((n + nt - 1) / nt);
  std::vector<std::thread> th;
  th.reserve(nt);
  for (unsigned t = 0; t < nt; ++t) {
    const auto off = static_cast<T>(chunk * t);
    const T b = first + off;
    if (b >= last) break;
    const T e = std::min<T>(last, static_cast<T>(first + off + static_cast<T>(chunk)));
    th.emplace_back([&f, b, e] { f(blocked_range<T>(b, e)); });
  }
  for (auto &x : th) x.join();
}
}  // namespace tbb
