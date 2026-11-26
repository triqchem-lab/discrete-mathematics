// 垫片分块回归测试(Wang 框架手工构建用, 见 ../README.md)。
//
// 背景: 2026-11-27 实测, tbb 垫片的 parallel_for 分块曾有差一错误 —— 只有最后一个线程把
// 区间终点钳到 last, 而分块不整除且末块起点 >= last 时该线程直接不运行, 于是倒数第二块的
// 终点越过 last(n = 13、8 线程时块长 2, 区间成了 [12, 14))。下标越界读到零向量, 令 F₃
// 下界搜索在 dim = 6 处 FATAL。F₂ 的各维轨道数(1, 3, 14, 68, 162)恰好都不触发, 所以回归
// 当时没暴露。
//
// 本测试对线程数 × 区间长度逐组合验证:
//   parallel_for(first, last, f)     每个下标恰好访问一次, 且无越界;
//   parallel_for(blocked_range, f)   每个块都在 [first, last) 内, 每个下标恰好访问一次;
//   parallel_reduce(range, …)        结果等于串行结果。
// 线程数由环境变量 SHIM_THREADS 指定(缺省 = 硬件并发数), 由 run.sh 对 1..8 各跑一遍。
#include <atomic>
#include <cstdint>
#include <cstdio>
#include <vector>

#include "tbb/blocked_range.h"
#include "tbb/parallel_for.h"
#include "tbb/parallel_reduce.h"

int main() {
  int failures = 0;
  for (int n = 0; n <= 40; ++n) {
    // ---- parallel_for(first, last, f) ----
    {
      std::vector<std::atomic<int>> count(static_cast<size_t>(n));
      std::atomic<int> out_of_range{0};
      tbb::parallel_for(0, n, [&](int i) {
        if (i < 0 || i >= n) {
          out_of_range.fetch_add(1);
          return;
        }
        count[static_cast<size_t>(i)].fetch_add(1);
      });
      for (int i = 0; i < n; ++i) {
        if (count[static_cast<size_t>(i)].load() != 1) {
          if (failures++ < 10)
            std::printf("FAIL index-form n=%d i=%d visits=%d\n", n, i, count[static_cast<size_t>(i)].load());
        }
      }
      if (out_of_range.load() != 0) {
        if (failures++ < 10) std::printf("FAIL index-form n=%d out_of_range=%d\n", n, out_of_range.load());
      }
    }
    // ---- parallel_for(blocked_range, f): 非零起点, 顺带验证块界 ----
    {
      const std::size_t first = 5;
      const std::size_t last = first + static_cast<std::size_t>(n);
      std::vector<std::atomic<int>> count(static_cast<size_t>(n));
      std::atomic<int> bad_chunk{0};
      tbb::parallel_for(tbb::blocked_range<std::size_t>(first, last),
                        [&](const tbb::blocked_range<std::size_t> &r) {
                          if (r.begin() < first || r.end() > last || r.begin() > r.end()) bad_chunk.fetch_add(1);
                          for (std::size_t i = r.begin(); i < r.end(); ++i) {
                            if (i < first || i >= last) {
                              bad_chunk.fetch_add(1);
                              continue;
                            }
                            count[i - first].fetch_add(1);
                          }
                        });
      for (int i = 0; i < n; ++i) {
        if (count[static_cast<size_t>(i)].load() != 1) {
          if (failures++ < 10)
            std::printf("FAIL range-form n=%d i=%d visits=%d\n", n, i, count[static_cast<size_t>(i)].load());
        }
      }
      if (bad_chunk.load() != 0) {
        if (failures++ < 10) std::printf("FAIL range-form n=%d bad_chunk=%d\n", n, bad_chunk.load());
      }
    }
    // ---- parallel_reduce(range, init, f, red) ----
    {
      const std::uint64_t got = tbb::parallel_reduce(
          tbb::blocked_range<std::size_t>(0, static_cast<std::size_t>(n)), std::uint64_t{0},
          [](const tbb::blocked_range<std::size_t> &r, std::uint64_t init) {
            for (std::size_t i = r.begin(); i != r.end(); ++i) init += static_cast<std::uint64_t>(i) + 1;
            return init;
          },
          [](std::uint64_t a, std::uint64_t b) { return a + b; });
      const std::uint64_t want = static_cast<std::uint64_t>(n) * static_cast<std::uint64_t>(n + 1) / 2;
      if (got != want) {
        if (failures++ < 10) std::printf("FAIL reduce n=%d got=%llu want=%llu\n", n, (unsigned long long)got, (unsigned long long)want);
      }
    }
  }
  if (failures == 0) {
    std::printf("OK shim chunking (SHIM_THREADS=%s)\n", std::getenv("SHIM_THREADS") ? std::getenv("SHIM_THREADS") : "unset");
    return 0;
  }
  std::printf("FAILED shim chunking: %d failures\n", failures);
  return 1;
}
