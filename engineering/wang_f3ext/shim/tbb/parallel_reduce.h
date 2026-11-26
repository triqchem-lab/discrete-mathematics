#pragma once
// 区间终点一律钳到 last: 分块不整除且末块起点 >= last 时, 倒数第二块不得越过 last
// (2026-11-27 实测: n=13/8 线程时旧写法给出 [12,14) → 越界读 → F3 下界搜索 FATAL)。
// tbb 垫片(手工构建用): parallel_reduce 的 std::thread 实现。
// 语义: 把 range 分成若干连续块, 每块调用 f(blocked_range(块), init), 各块结果按 reduce 依次结合到 init 上
// (与 oneTBB 的 parallel_reduce(range, identity, func, reduce) 对可结合、可交换的 reduce 一致)。
#include <thread>
#include <type_traits>
#include <vector>

#include "tbb/blocked_range.h"
#include "tbb/parallel_for.h"

namespace tbb {
template <class T, class Value, class Func, class Reduce>
Value parallel_reduce(const blocked_range<T> &range, Value init, const Func &f,
                      const Reduce &red) {
  const T first = range.begin();
  const T last = range.end();
  if (last <= first) return init;
  if (shim::Depth() >= 1) return f(range, init);
  shim::DepthGuard g(shim::Depth());
  const auto n = static_cast<std::make_unsigned_t<T>>(last - first);
  unsigned nt = shim::MaxThreads();
  if (n < nt) nt = static_cast<unsigned>(n);
  if (nt <= 1) return f(range, init);
  const auto chunk = static_cast<std::make_unsigned_t<T>>((n + nt - 1) / nt);
  std::vector<Value> vals(nt, init);
  std::vector<std::thread> th;
  th.reserve(nt);
  unsigned started = 0;
  for (unsigned t = 0; t < nt; ++t) {
    const auto off = static_cast<T>(chunk * t);
    const T b = first + off;
    if (b >= last) break;
    const T e = std::min<T>(last, static_cast<T>(first + off + static_cast<T>(chunk)));
    th.emplace_back([&f, &vals, t, b, e] {
      vals[t] = f(blocked_range<T>(b, e), vals[t]);
    });
    ++started;
  }
  for (auto &x : th) x.join();
  Value result = init;
  for (unsigned t = 0; t < started; ++t) result = red(result, vals[t]);
  return result;
}
}  // namespace tbb
