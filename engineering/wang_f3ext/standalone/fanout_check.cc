// fanout_check.cc —— 扇出存储(SOVEREIGN_F3_FANOUT, 见 search/orbit_map.h 的 F₃ 分支)的见证方程对拍。
//
// 建一张只含「互不等价的随机子空间」的 OrbitMap(同一个轨道只 Set 一次, 与流水线一致), 再对这些子空间在群作用下的
// 随机像 q 调 Get, 对每一次命中检查:
//   Canon(store.ApplyInverse(ws, query.Apply(wq, q))) == 轨道代表(子空间本身), 且 rank 相同, 见证在群里。
// 扇出 >= 2 时首命中与见证都会变(见证是 (L_f⁻¹·L_e, t)), 但这条方程不变 —— 它正是验证端
// (verifier/backtracking_verifier.h 的 CanonicalFromWitness, 以及独立核对器)所依赖的东西。
//
// 编译(与 get_simd_check.cc 相同): clang++ -std=c++23 -O2 -I<shim> -I<WANG_REPO> fanout_check.cc <WANG_REPO>/core/dynamic_matrix.cc -pthread
// 运行: ./fanout_check [轨道数=20] [每轨道 Get 次数=30]   —— 有任何一次不满足则 exit 1
// 环境: SOVEREIGN_F3_FANOUT=1(缺省) / 8 / 16 ... 各跑一遍。输出最后一行给出一次 Get 的平均耗时。
// 注意: 「每个轨道只放一条代表」是对拍件自己的要求 —— 两条同轨道的「代表」会让 OrbitMap(扇出后左乘像落到
// 同一 H-轨道的另一个 store-轨道上)与只存普通像的参考给出不同的 rank(2026-11-27 在 get_simd_check 里踩到)。
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <string>
#include <unordered_set>
#include <vector>

#include "core/constraints.h"
#include "core/rank_f3_fast.h"
#include "problems/matrix/symmetry.h"
#include "search/orbit_map.h"

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
std::string Show(const Cons9 &c) {
  std::string s;
  for (const Vec9 &v : c) { s += "["; for (int k = 0; k < 9; ++k) s += std::to_string(v[k].value); s += "]"; }
  return s;
}
} // namespace

int main(int argc, char **argv) {
  const int reps = argc > 1 ? std::atoi(argv[1]) : 20;
  const int gets = argc > 2 ? std::atoi(argv[2]) : 30;
  Group g;
  OrbitMap<P3> map(&g);
  std::mt19937_64 rng(20261127);
  // 已有轨道的全部普通像(参考集合, 用来保证每个轨道只 Set 一次)
  std::unordered_set<Cons9, Hash9> seen;
  std::vector<std::pair<Cons9, int>> reps_vec;
  long bad = 0, tried = 0;
  double hit_pos = 0; long hits = 0;
  while (static_cast<int>(reps_vec.size()) < reps) {
    Cons9 c = RandomSubspace(rng, 1 + static_cast<int>(rng() % 8));
    bool dup = false;
    Cons9 img;
    for (int i = 0; i < g.query.Size() && !dup; ++i) {
      img.clear();
      for (const Vec9 &v : c) img.push_back(g.query.Apply(g.query.At(i), v));
      if (seen.count(Canon(img))) dup = true;
    }
    if (dup) continue;
    for (int i = 0; i < g.query.Size(); ++i) {
      img.clear();
      for (const Vec9 &v : c) img.push_back(g.query.Apply(g.query.At(i), v));
      seen.insert(Canon(img));
    }
    const int rank = static_cast<int>(rng() % 20);
    map.Set(c, rank);
    reps_vec.emplace_back(c, rank);
  }
  for (const auto &[c, rank] : reps_vec) {
    for (int t = 0; t < gets; ++t) {
      const QElem e = g.query.At(static_cast<int>(rng() % static_cast<std::uint64_t>(g.query.Size())));
      const SElem s = g.store.At(static_cast<int>(rng() % static_cast<std::uint64_t>(g.store.Size())));
      Cons9 q;
      for (const Vec9 &v : c) q.push_back(g.store.Apply(s, g.query.Apply(e, v)));
      QElem wq{}; SElem ws{};
      const auto t0 = std::chrono::steady_clock::now();
      const int r = map.Get(q, &wq, &ws);
      hit_pos += std::chrono::duration<double, std::micro>(std::chrono::steady_clock::now() - t0).count();
      ++hits;
      Cons9 back;
      for (const Vec9 &v : q) back.push_back(g.store.ApplyInverse(ws, g.query.Apply(wq, v)));
      back = Canon(back);
      ++tried;
      if (!(back == c && r == rank && g.query.Contains(wq) && g.store.Contains(ws))) {
        if (bad < 5) {
          std::printf("BAD rank=%d/%d c=%s\n  e=(l=%u,t=%u) s=%u wq=(l=%u,t=%u) ws=%u\n  got=%s\n",
                      r, rank, Show(c).c_str(), e.l, e.transpose, s, wq.l, wq.transpose, ws, Show(back).c_str());
        }
        ++bad;
      }
    }
  }
  std::printf("fanout check: reps=%zu gets=%ld bad=%ld avg Get %.1f us\n", reps_vec.size(), tried, bad, hit_pos / hits);
  return bad ? 1 : 0;
}
