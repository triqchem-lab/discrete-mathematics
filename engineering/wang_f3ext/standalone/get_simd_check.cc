// get_simd_check.cc — F₃ 批量探针内核(core/get_f3_simd.h)的对拍 + 微基准。
//
// A. 块内核: NEON 版 vs 标量版(独立实现), 随机 q / 真实 Query 元素, 输出逐位相同(行、主元标志、标签);
//    并核对标量版自身的输出 = 「逐个探针用框架的 query.Apply + GaussJordanRREF 算出的规范形」。
// B. OrbitMap 端到端: 批量版 Get vs 原标量逻辑(在测试里独立重写: 逐个 Query 元素求规范形再查表),
//    对同一 (q, 表) 必须返回同一首命中下标 / 界 / 见证。含无假阴性测试: 对若干已存键, 枚举全部
//    22464 个 Query 元素, 每个得到的 q 都必须查得到。
// C. ProbeAll 对随机 q(多数不在任何轨道里)的结果必须与标量逻辑一致: 同样未命中, 或同一命中。
// D. 微基准: 一次 Get 的耗时, 标量 vs 批量。
// E. 重复行: 回溯搜索的链上同一个候选可以重复出现, 查轨道时 q 里会有重复行 / 相关行。
//    Get(q) 只应依赖 q 的行空间: 把一个已存键的行随机重复、随机线性组合之后, Get 必须给出
//    与「去重后的规范行」完全相同的结果(界 + 一对见证), 且与标量逻辑一致。
//    这是 search/rank_lower_bound_backtracking.h 里「去重键」优化的依据。
// F. 扇出(SOVEREIGN_F3_FANOUT >= 2): Set 多存左乘像、探针顺序交错之后, 首命中与见证都会变。B / E 两节在扇出模式下
//    不再要求「同一个下标、同一对见证」, 改为比见证方程: 两边交出的见证必须把 q 映到同一个轨道代表, rank 相同。
//    扇出为 1(缺省)时仍按逐位相同来比。main 的第一行输出 fanout=N。
//
// 编译: clang++ -std=c++23 -O3 -I<shim> -I<WANG_REPO> get_simd_check.cc <WANG_REPO>/core/dynamic_matrix.cc
// 运行: ./get_simd_check   —— 全部相同则 exit 0
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <unordered_map>
#include <vector>

#include "core/constraints.h"
#include "core/get_f3_simd.h"
#include "core/rank_f3_fast.h"
#include "problems/matrix/symmetry.h"
#include "search/orbit_map.h"

#if !SOVEREIGN_F3_NEON
#error "get_simd_check 需要在 ARM NEON 机器上编译(对拍 NEON 内核)"
#endif

namespace {

using Vec9 = GFVec<3, 1, 9>;
using Cons9 = Constraints<3, 1, 9>;
using Hash9 = ConstraintsHash<3, 1, 9>;

struct P3 {
  static constexpr int kP = 3, kM = 1, kNA = 9;
  using SymmetryGroup = matrix::SymmetryGroupFq<3, 3, 3, 3>;
};
using Group = P3::SymmetryGroup;
using QElem = Group::QuerySet::Elem;
using SElem = Group::StoreSet::Elem;

Cons9 Canon(Cons9 rows) {
  const int r = GaussJordanRREF<3, 1, 9>(&rows);
  rows.erase(rows.begin(), rows.end() - r);
  return rows;
}

Cons9 RandomSubspace(std::mt19937_64 &rng, int dim) {
  while (true) {
    Cons9 rows;
    for (int i = 0; i < dim; ++i) {
      Vec9 v;
      for (int c = 0; c < 9; ++c) v.Set(c, GF<3, 1>{static_cast<std::uint8_t>(rng() % 3)});
      rows.push_back(v);
    }
    if (GaussJordanRREF<3, 1, 9>(&rows) != dim) continue;
    rows.erase(rows.begin(), rows.end() - dim);
    return rows;
  }
}

Cons9 ApplyQuery(const Group &g, const QElem &e, const Cons9 &rows) {
  Cons9 img;
  for (const Vec9 &v : rows) img.push_back(g.query.Apply(e, v));
  return Canon(img);
}

struct Val {
  int rank;
  SElem store;
};
using RefTable = std::unordered_map<Cons9, Val, Hash9>;

// 镜像 OrbitMap::Set: 每个.store 元素作用在代表上, 规范形作键, 后写覆盖
void RefInsert(const Group &g, RefTable *ref, const Cons9 &c, int rank) {
  for (int j = 0; j < g.store.Size(); ++j) {
    const SElem s = g.store.At(j);
    Cons9 img;
    for (const Vec9 &v : c) img.push_back(g.store.Apply(s, v));
    (*ref)[Canon(img)] = Val{rank, s};
  }
}

// 原标量 Get 的逻辑(独立重写): 返回首命中的下标, 没有则 −1
int RefGet(const Group &g, const RefTable &ref, const Cons9 &q, int *rank, SElem *store) {
  for (int i = 0; i < g.query.Size(); ++i) {
    const auto it = ref.find(ApplyQuery(g, g.query.At(i), q));
    if (it != ref.end()) {
      *rank = it->second.rank;
      *store = it->second.store;
      return i;
    }
  }
  return -1;
}

void BuildRef(const Group &g, RefTable *ref, OrbitMap<P3> *map, std::mt19937_64 &rng, int reps,
              std::vector<Cons9> *keys) {
  // 流水线里每个轨道只 Set 一次, 这里也要这样: 扇出之后左乘像会落到同一 H-轨道的另一个 store-轨道上,
  // 若两条「代表」其实同属一个轨道, OrbitMap 与只存普通像的参考表就会给出不同的 rank(2026-11-27 实测踩到)。
  for (int k = 0; k < reps; ++k) {
    Cons9 c;
    bool dup;
    do {
      c = RandomSubspace(rng, 1 + static_cast<int>(rng() % 8));
      dup = false;
      for (int i = 0; i < g.query.Size() && !dup; ++i) {
        dup = ref->find(ApplyQuery(g, g.query.At(i), c)) != ref->end();
      }
    } while (dup);
    const int rank = static_cast<int>(rng() % 20);
    map->Set(c, rank);
    RefInsert(g, ref, c, rank);
    keys->push_back(c);
  }
}

// ---- A ----
long CheckBlockKernel(const Group &g, std::mt19937_64 &rng, long trials, long *blocks) {
  sovereign_f3::QuerySoA soa;
  sovereign_f3::BuildQuerySoA(
      g.query.Size(),
      [&](int i, std::uint8_t *d, std::uint8_t *t) {
        const QElem e = g.query.At(i);
        sovereign_f3::DigitsOfData3(e.l, d);
        *t = static_cast<std::uint8_t>(e.transpose ? 1 : 0);
      },
      &soa);
  sovereign_f3::BlockOut a, b;
  long bad = 0;
  for (long t = 0; t < trials; ++t) {
    const int n = 1 + static_cast<int>(rng() % 9);
    const Cons9 q = RandomSubspace(rng, n);
    std::uint8_t V[9][9];
    for (int r = 0; r < n; ++r) {
      for (int c = 0; c < 9; ++c) V[r][c] = q[static_cast<std::size_t>(r)][c].value;
    }
    const int e0 = static_cast<int>(rng() % static_cast<std::uint64_t>(g.query.Size() - 16));
    sovereign_f3::BlockKernelScalar(V, n, soa, e0, &a);
    sovereign_f3::BlockKernelNeon(V, n, soa, e0, &b);
    ++*blocks;
    for (int p = 0; p < 16; ++p) {
      Cons9 key;
      for (int col = 0; col < 9; ++col) {
        if (a.found[col][p] != b.found[col][p]) ++bad;
        for (int c = 0; c < 9; ++c) {
          if (a.row[col][c][p] != b.row[col][c][p]) ++bad;
        }
        if (!a.found[col][p]) continue;
        Vec9 row;
        for (int c = 0; c < 9; ++c) row.Set(c, GF<3, 1>{a.row[col][c][p]});
        key.push_back(row);
      }
      if (a.tag[p] != b.tag[p]) ++bad;
      if (key != ApplyQuery(g, g.query.At(e0 + p), q)) ++bad;
      if (sovereign_f3::KeyTag(key) != a.tag[p]) ++bad;
    }
  }
  return bad;
}

int g_fanout = 1;  // main 里按环境变量 SOVEREIGN_F3_FANOUT 设置, 与 OrbitMap 读的是同一个变量

// 见证 (wq, ws) 把 rows 映到的轨道代表: Canon(store.ApplyInverse(ws, query.Apply(wq, rows)))
Cons9 WitnessRep(const Group &g, const Cons9 &rows, QElem wq, SElem ws) {
  Cons9 back;
  for (const Vec9 &v : rows) back.push_back(g.store.ApplyInverse(ws, g.query.Apply(wq, v)));
  return Canon(back);
}

// map 交出的见证 (wq, ws) 与参考逻辑交出的见证 (下标 ri 的 query 元素, rs) 是否指向同一个轨道。
// 扇出为 1 时 OrbitMap 与参考逻辑的探针顺序相同, 要求逐位一致; 否则比见证方程。
bool SameOrbit(const Group &g, const Cons9 &q, QElem wq, SElem ws, int ri, SElem rs) {
  if (g_fanout == 1) {
    return ri >= 0 && wq.l == g.query.At(ri).l && wq.transpose == g.query.At(ri).transpose && ws == rs;
  }
  if (ri < 0 || !g.query.Contains(wq) || !g.store.Contains(ws)) {
    return false;
  }
  return WitnessRep(g, q, wq, ws) == WitnessRep(g, q, g.query.At(ri), rs);
}
// ---- B ----
long CheckOrbitMap(const Group &g, std::mt19937_64 &rng, int reps, int no_miss_keys, long *gets,
                   long *tall) {
  OrbitMap<P3> map(&g);
  RefTable ref;
  std::vector<Cons9> reps_vec;
  BuildRef(g, &ref, &map, rng, reps, &reps_vec);
  std::vector<Cons9> keys;
  for (const auto &kv : ref) keys.push_back(kv.first);
  long bad = 0;
  for (long t = 0; t < 3000; ++t) {
    const Cons9 &key = keys[static_cast<std::size_t>(rng() % keys.size())];
    const QElem e = g.query.At(static_cast<int>(rng() % static_cast<std::uint64_t>(g.query.Size())));
    Cons9 q = ApplyQuery(g, e, key);
    if (rng() % 2 == 0) {
      // 一半的查询加上 1–3 条落在跨度里的相关行: 回溯搜索会把多条额外行加在基上, q 可以超过 9 行。
      const int extra = 1 + static_cast<int>(rng() % 3);
      for (int x = 0; x < extra; ++x) {
        Vec9 row;
        for (const Vec9 &v : q) {
          const int a = static_cast<int>(rng() % 3);
          for (int c = 0; c < 9; ++c) {
            row.Set(c, GF<3, 1>{static_cast<std::uint8_t>((row[c].value + a * v[c].value) % 3)});
          }
        }
        q.push_back(row);
      }
      if (q.size() > 9) ++*tall;
    }
    int rr = 0, ri = 0;
    SElem rs{}, ws{};
    QElem wq{};
    const int mr = map.Get(q, &wq, &ws);
    ri = RefGet(g, ref, q, &rr, &rs);
    ++*gets;
    if (ri < 0 || mr != rr || !SameOrbit(g, q, wq, ws, ri, rs)) {
      if (bad < 5) std::printf("GET MISMATCH: map=(%d) ref=(%d,%d)\n", mr, ri, rr);
      ++bad;
    }
  }
  // 无假阴性: 每个键 × 全部 Query 元素
  for (int k = 0; k < no_miss_keys; ++k) {
    const Cons9 &key = keys[static_cast<std::size_t>(rng() % keys.size())];
    for (int i = 0; i < g.query.Size(); ++i) {
      const Cons9 q = ApplyQuery(g, g.query.At(i), key);
      QElem wq{};
      SElem ws{};
      int rr = 0, ri = 0;
      SElem rs{};
      ri = RefGet(g, ref, q, &rr, &rs);
      const int mr = map.Get(q, &wq, &ws);  // 查不到会 FATAL(abort), 走不到下面
      ++*gets;
      if (ri < 0 || mr != rr) ++bad;
      // 见证必须满足命中方程: Q·q ≡ S·c, 其中 c 是 q 所在轨道的代表(它是已存的某个键的来源)。
      Cons9 lhs, rhs;
      for (const Vec9 &v : q) lhs.push_back(g.query.Apply(wq, v));
      lhs = Canon(lhs);
      Cons9 back;
      for (const Vec9 &v : lhs) back.push_back(g.store.ApplyInverse(ws, v));
      const Cons9 c = Canon(back);
      for (const Vec9 &v : c) rhs.push_back(g.store.Apply(ws, v));
      if (Canon(rhs) != lhs || ref.count(c) == 0 || ref.at(c).rank != mr) ++bad;
    }
  }
  return bad;
}

// ---- C ----
long CheckProbeAll(const Group &g, std::mt19937_64 &rng, int reps, long trials, long *misses) {
  RefTable ref;
  OrbitMap<P3> map(&g);
  std::vector<Cons9> reps_vec;
  BuildRef(g, &ref, &map, rng, reps, &reps_vec);
  std::vector<sovereign_f3::FlatTagTable> flat(10);
  for (const auto &kv : ref) flat[kv.first.size()].Insert(sovereign_f3::KeyTag(kv.first));
  sovereign_f3::QuerySoA soa;
  sovereign_f3::BuildQuerySoA(
      g.query.Size(),
      [&](int i, std::uint8_t *d, std::uint8_t *t) {
        const QElem e = g.query.At(i);
        sovereign_f3::DigitsOfData3(e.l, d);
        *t = static_cast<std::uint8_t>(e.transpose ? 1 : 0);
      },
      &soa);
  long bad = 0;
  for (long t = 0; t < trials; ++t) {
    const Cons9 q = RandomSubspace(rng, 1 + static_cast<int>(rng() % 8));
    int hq = -2, rr = 0;
    SElem hs{}, rs{};
    const int pr = sovereign_f3::ProbeAll(
        q, soa, flat,
        [&](const Cons9 &key, SElem *store) -> int {
          const auto it = ref.find(key);
          if (it == ref.end()) return -1;
          *store = it->second.store;
          return it->second.rank;
        },
        &hq, &hs);
    const int ri = RefGet(g, ref, q, &rr, &rs);
    if (pr < 0) ++*misses;
    if ((pr < 0) != (ri < 0) || (pr >= 0 && (pr != rr || hq != ri || hs != rs))) {
      if (bad < 5) std::printf("PROBE MISMATCH: probe=(%d,%d) ref=(%d,%d)\n", pr, hq, ri, rr);
      ++bad;
    }
  }
  return bad;
}

// ---- E ----
long CheckRepeatedRows(const Group &g, std::mt19937_64 &rng, int reps, long trials) {
  OrbitMap<P3> map(&g);
  RefTable ref;
  std::vector<Cons9> reps_vec;
  BuildRef(g, &ref, &map, rng, reps, &reps_vec);
  std::vector<Cons9> keys;
  for (const auto &kv : ref) keys.push_back(kv.first);
  long bad = 0, tall = 0;
  for (long t = 0; t < trials; ++t) {
    const Cons9 &key = keys[static_cast<std::size_t>(rng() % keys.size())];
    Cons9 q = key;
    const int extra = static_cast<int>(rng() % 7);  // 0–6 条多余的行
    for (int x = 0; x < extra; ++x) {
      if (rng() % 2 == 0) {
        // 重复一行
        q.push_back(key[static_cast<std::size_t>(rng() % key.size())]);
      } else {
        // key 各行的随机线性组合(系数 0..2, 可能为零行)
        Vec9 row;
        for (const Vec9 &v : key) {
          const int a = static_cast<int>(rng() % 3);
          for (int c = 0; c < 9; ++c) {
            row.Set(c, GF<3, 1>{static_cast<std::uint8_t>((row[c].value + a * v[c].value) % 3)});
          }
        }
        q.push_back(row);
      }
    }
    std::shuffle(q.begin(), q.end(), rng);  // 行序也打乱
    if (q.size() > 9) ++tall;
    QElem wq{}, wq0{};
    SElem ws{}, ws0{};
    const int r1 = map.Get(q, &wq, &ws);
    const int r0 = map.Get(key, &wq0, &ws0);
    int rr = 0, ri = 0;
    SElem rs{};
    ri = RefGet(g, ref, q, &rr, &rs);
    bool ok;
    if (g_fanout == 1) {
      ok = !(r1 != r0 || wq.l != wq0.l || wq.transpose != wq0.transpose || ws != ws0 || ri < 0 || r1 != rr ||
             wq.l != g.query.At(ri).l || wq.transpose != g.query.At(ri).transpose || ws != rs);
    } else {
      // 扇出: q(含重复 / 相关行)与 key(规范行)的见证可以不同, 但必须落在同一个轨道代表上, 且与参考一致。
      ok = ri >= 0 && r1 == r0 && r1 == rr && g.query.Contains(wq) && g.query.Contains(wq0) &&
           WitnessRep(g, q, wq, ws) == WitnessRep(g, key, wq0, ws0) &&
           WitnessRep(g, q, wq, ws) == WitnessRep(g, q, g.query.At(ri), rs);
    }
    if (!ok) {
      if (bad < 5) std::printf("REPEAT MISMATCH: rows=%zu raw=(%d) dedup=(%d) ref=(%d,%d)\n", q.size(), r1, r0, ri, rr);
      ++bad;
    }
  }
  return bad;
}

// ---- D ----
void Bench(const Group &g, std::mt19937_64 &rng, int reps, int qdim, int iters) {
  OrbitMap<P3> map(&g);
  RefTable ref;
  std::vector<Cons9> reps_vec;
  BuildRef(g, &ref, &map, rng, reps, &reps_vec);
  std::vector<Cons9> keys;
  for (const auto &kv : ref) keys.push_back(kv.first);
  std::vector<Cons9> qs;
  for (int t = 0; t < iters; ++t) {
    const Cons9 &key = keys[static_cast<std::size_t>(rng() % keys.size())];
    qs.push_back(ApplyQuery(g, g.query.At(static_cast<int>(rng() % static_cast<std::uint64_t>(g.query.Size()))), key));
  }
  volatile int sink = 0;
  auto t0 = std::chrono::steady_clock::now();
  for (const Cons9 &q : qs) sink += map.Get(q, nullptr, nullptr);
  auto t1 = std::chrono::steady_clock::now();
  const int scalar_iters = std::max(1, iters / 20);
  for (int t = 0; t < scalar_iters; ++t) {
    int rr = 0;
    SElem rs{};
    sink += RefGet(g, ref, qs[static_cast<std::size_t>(t)], &rr, &rs);
  }
  auto t2 = std::chrono::steady_clock::now();
  // 全未命中的代价(全部 22464 个探针): 取一个不在任何轨道里的 q
  Cons9 miss;
  while (true) {
    miss = RandomSubspace(rng, qs.front().size());
    int rr = 0;
    SElem rs{};
    if (RefGet(g, ref, miss, &rr, &rs) < 0) break;
  }
  auto m0 = std::chrono::steady_clock::now();
  sink += RefGet(g, ref, miss, nullptr, nullptr);
  auto m1 = std::chrono::steady_clock::now();
  std::printf("bench-miss: scalar full scan %.0f ns → %.1f ns/probe",
              std::chrono::duration<double, std::nano>(m1 - m0).count(),
              std::chrono::duration<double, std::nano>(m1 - m0).count() / g.query.Size());
  // 批量版的满扫描(同一张表: 权威表 ref + 标签表)
  {
    std::vector<sovereign_f3::FlatTagTable> flat(10);
    for (const auto &kv : ref) flat[kv.first.size()].Insert(sovereign_f3::KeyTag(kv.first));
    sovereign_f3::QuerySoA soa;
    sovereign_f3::BuildQuerySoA(
        g.query.Size(),
        [&](int i, std::uint8_t *d, std::uint8_t *tr) {
          const QElem e = g.query.At(i);
          sovereign_f3::DigitsOfData3(e.l, d);
          *tr = static_cast<std::uint8_t>(e.transpose ? 1 : 0);
        },
        &soa);
    int hq = -2;
    SElem hs{};
    auto b0 = std::chrono::steady_clock::now();
    const int pr = sovereign_f3::ProbeAll(
        miss, soa, flat,
        [&](const Cons9 &key, SElem *store) -> int {
          const auto it = ref.find(key);
          if (it == ref.end()) return -1;
          *store = it->second.store;
          return it->second.rank;
        },
        &hq, &hs);
    auto b1 = std::chrono::steady_clock::now();
    const double ns = std::chrono::duration<double, std::nano>(b1 - b0).count();
    std::printf("; batched full scan %.0f ns → %.1f ns/probe (rc=%d)\n", ns, ns / g.query.Size(), pr);
  }
  const double batchNs = std::chrono::duration<double, std::nano>(t1 - t0).count() / iters;
  const double scalarNs = std::chrono::duration<double, std::nano>(t2 - t1).count() / scalar_iters;
  std::printf("bench: table %d reps (%zu keys), |q| = %d → Get: batched %.0f ns, scalar %.0f ns (%.1fx)\n",
              reps, keys.size(), qdim, batchNs, scalarNs, scalarNs / batchNs);
  (void)sink;
}

} // namespace

int main(int argc, char **argv) {
  const long block_trials = argc > 1 ? std::atol(argv[1]) : 2000;
  if (const char *s = std::getenv("SOVEREIGN_F3_FANOUT")) {
    g_fanout = std::max(1, std::atoi(s));
  }
  Group g;
  std::mt19937_64 rng(20261127);
  std::printf("query=%d store=%d NEON=%d fanout=%d\n", g.query.Size(), g.store.Size(), SOVEREIGN_F3_NEON,
              g_fanout);
  long blocks = 0, gets = 0, misses = 0;
  const long a = CheckBlockKernel(g, rng, block_trials, &blocks);
  std::printf("A block kernel: blocks=%ld lanes=%ld mismatches=%ld\n", blocks, blocks * 16, a);
  long tall = 0;
  const long b = CheckOrbitMap(g, rng, 14, 2, &gets, &tall);
  std::printf("B orbit map (14 reps, dim-2-level table): gets=%ld (of which %ld with >9 rows) mismatches=%ld\n",
              gets, tall, b);
  const long c = CheckProbeAll(g, rng, 14, 300, &misses);
  std::printf("C probe-all (14 reps): trials=300 misses=%ld mismatches=%ld\n", misses, c);
  const long e = CheckRepeatedRows(g, rng, 14, 2000);
  std::printf("E repeated rows (14 reps): trials=2000 mismatches=%ld\n", e);
  Bench(g, rng, 14, 3, 20000);
  Bench(g, rng, 84, 4, 20000);
  Bench(g, rng, 266, 5, 4000);
  const bool ok = a == 0 && b == 0 && c == 0 && e == 0;
  std::printf("%s\n", ok ? "OK" : "FAILED");
  return ok ? 0 : 1;
}
