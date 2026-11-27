// apply_check.cc — F₃ 3×3 对称群作用的全枚举对拍: 框架实现（含 core/rank_f3_fast.h 的数位运算快路径）
// vs 独立写的朴素实现（直接按 X·R、L·τᵗ(X) 循环, 不经任何查表）。
//
// 背景: OrbitMap::Get 的每次探针要对约束组的每一行做一次 query.Apply; 微基准显示这一步
// 占探针时间约 3/4（表驱动的逐行打包/解包 + 查表）。快路径把它换成直接的 3×3 数位运算。
// 这里把全部 3^9 = 19683 个向量 × 全部群元（store 11232、query 22464）逐一比对,
// 并核对 ApplyInverse ∘ Apply = id 与单位元。
//
// 编译（需要上游副本 WANG_REPO 已打补丁, 以及本目录上一级的 shim/）:
//   clang++ -std=c++23 -O3 -DNDEBUG -w -I<shim> -I<WANG_REPO> apply_check.cc \
//            <WANG_REPO>/core/dynamic_matrix.cc -o apply_check
// 运行: ./apply_check [步长, 缺省 1 = 全部 19683 个向量]   —— 全部相等则 exit 0
//   全量约 40 s（空闲 8 核上单线程约 45 s 用户态）; unittest 用步长 17 做抽样, 全量由 WANG_SLOW=1 门控。
#include <cstdint>
#include <cstdio>
#include <cstdlib>

#include "core/constraints.h"
#include "problems/matrix/symmetry.h"

namespace {

using Group = matrix::SymmetryGroupFq<3, 3, 3, 3>;
using Vec = GFVec<3, 1, 9>;
using QElem = Group::QuerySet::Elem;
using SElem = Group::StoreSet::Elem;

// ---- 独立参考实现 ----
int Digit(std::uint32_t e, int place) {
  std::uint32_t p = 1;
  for (int t = 0; t < place; ++t) p *= 3;
  return static_cast<int>((e / p) % 3);
}

std::uint8_t V[3][3];

void Load(const Vec &v) {
  for (int i = 0; i < 3; ++i) {
    for (int j = 0; j < 3; ++j) V[i][j] = v[i * 3 + j].value;
  }
}

Vec Make(const std::uint8_t w[9]) {
  Vec r;
  for (int k = 0; k < 9; ++k) r.Set(k, GF<3, 1>{w[k]});
  return r;
}

Vec StoreRef(SElem r, const Vec &v) {
  Load(v);
  int R[3][3];
  for (int k = 0; k < 3; ++k)
    for (int j = 0; j < 3; ++j) R[k][j] = Digit(r, k * 3 + j);
  std::uint8_t w[9];
  for (int i = 0; i < 3; ++i)
    for (int j = 0; j < 3; ++j) {
      int s = 0;
      for (int k = 0; k < 3; ++k) s += V[i][k] * R[k][j];
      w[i * 3 + j] = static_cast<std::uint8_t>(s % 3);
    }
  return Make(w);
}

Vec QueryRef(QElem e, const Vec &v) {
  Load(v);
  if (e.transpose) {
    for (int i = 0; i < 3; ++i)
      for (int j = i + 1; j < 3; ++j) std::swap(V[i][j], V[j][i]);
  }
  int L[3][3];
  for (int i = 0; i < 3; ++i)
    for (int k = 0; k < 3; ++k) L[i][k] = Digit(e.l, i * 3 + k);
  std::uint8_t w[9];
  for (int i = 0; i < 3; ++i)
    for (int j = 0; j < 3; ++j) {
      int s = 0;
      for (int k = 0; k < 3; ++k) s += L[i][k] * V[k][j];
      w[i * 3 + j] = static_cast<std::uint8_t>(s % 3);
    }
  return Make(w);
}

} // namespace

int main(int argc, char **argv) {
  static_assert(Group::kFast3, "本件针对 F₃ 3×3 的快路径");
  const std::uint32_t stride = argc > 1 ? static_cast<std::uint32_t>(std::atoi(argv[1])) : 1;
  Group g;
  long bad_store = 0, bad_query = 0, bad_inv = 0, bad_id = 0, total = 0;
  for (std::uint32_t vd = 0; vd < 19683; vd += stride) {
    Vec v;
    std::uint32_t d = vd;
    for (int k = 0; k < 9; ++k) {
      v.Set(k, GF<3, 1>{static_cast<std::uint8_t>(d % 3)});
      d /= 3;
    }
    for (int j = 0; j < g.store.Size(); ++j) {
      const SElem s = g.store.At(j);
      const Vec a = g.store.Apply(s, v);
      if (!(a == StoreRef(s, v))) ++bad_store;
      if (!(g.store.ApplyInverse(s, a) == v)) ++bad_inv;
    }
    if (!(g.store.Apply(g.store.Identity(), v) == v)) ++bad_id;
    for (int i = 0; i < g.query.Size(); ++i) {
      const QElem e = g.query.At(i);
      const Vec a = g.query.Apply(e, v);
      if (!(a == QueryRef(e, v))) ++bad_query;
      if (!(g.query.ApplyInverse(e, a) == v)) ++bad_inv;
    }
    if (!(g.query.Apply(g.query.Identity(), v) == v)) ++bad_id;
    ++total;
  }
  std::printf("apply check: vectors=%ld store=%d query=%d | mismatches: store=%ld query=%ld inverse=%ld identity=%ld\n",
              total, g.store.Size(), g.query.Size(), bad_store, bad_query, bad_inv, bad_id);
  const long expected = (19683 + stride - 1) / stride;
  const bool ok = bad_store == 0 && bad_query == 0 && bad_inv == 0 && bad_id == 0 && total == expected;
  std::printf("%s\n", ok ? "OK" : "FAILED");
  return ok ? 0 : 1;
}
