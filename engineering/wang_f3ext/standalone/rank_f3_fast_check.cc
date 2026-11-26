// rank_f3_fast_check.cc — F₃ 求秩 / 展平秩快路径（core/rank_f3_fast.h）与独立参考实现对拍 + 计时。
//
// 背景: Wang 框架的 DynamicMatrix<3,1>::Rank() 通用实现每次调用堆分配 + 全 Gauss–Jordan,
// RankLowerBoundFlatten 再做两次循环转置 + 三次堆分配; forced product 每次迭代约 20 µs。
// 本件用**独立写的**通用 Gauss–Jordan（求秩）与「转置 + 参考求秩」（展平秩）作参考,
// 在随机输入上逐个对拍, 并打印直方图（保证样本覆盖到各结果, 不是空转）。
//
// 编译（需要上游副本 WANG_REPO 已打补丁, 以及本目录上一级的 shim/）:
//   clang++ -std=c++23 -O3 -I<shim> -I<WANG_REPO> rank_f3_fast_check.cc \
//            <WANG_REPO>/core/dynamic_matrix.cc -o rank_f3_fast_check
// 另有一节核对退化归约的 F₃ 剪枝: 「只扫关于基极小的候选行」访问的超空间集合
//   == 「扫全部候选行」访问的超空间集合（对 dim 0..8 的随机基, 候选行全枚举）。
// 运行: ./rank_f3_fast_check [试验数, 缺省 200000]   —— 全部相等则 exit 0
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <set>
#include <vector>

#include "core/constraints.h"
#include "core/dynamic_matrix.h"
#include "core/gf_vec.h"
#include "core/rank_f3_fast.h"
#include "core/rank_lower_bound_flatten.h"

namespace {

// 独立写的参考: 完整 Gauss–Jordan（上面下面都消）, 与快路径没有共享代码。
int ReferenceRank(std::vector<std::vector<int>> rows) {
  const int n0 = static_cast<int>(rows.size());
  const int n1 = n0 > 0 ? static_cast<int>(rows[0].size()) : 0;
  int rank = 0;
  int pivot_col = 0;
  for (int row = 0; row < n0 && pivot_col < n1; ++row) {
    int pivot_row = -1;
    for (int r = row; r < n0; ++r) {
      if (rows[r][pivot_col] != 0) {
        pivot_row = r;
        break;
      }
    }
    if (pivot_row == -1) {
      ++pivot_col;
      --row;
      continue;
    }
    std::swap(rows[row], rows[pivot_row]);
    const int pivot = rows[row][pivot_col];
    if (pivot != 1) {
      const int inv = 2;  // 2⁻¹ = 2 (mod 3); pivot 只能是 2
      for (int c = 0; c < n1; ++c) rows[row][c] = (rows[row][c] * inv) % 3;
    }
    for (int r = 0; r < n0; ++r) {
      if (r == row) continue;
      const int c0 = rows[r][pivot_col];
      if (c0 == 0) continue;
      for (int col = 0; col < n1; ++col) {
        rows[r][col] = ((rows[r][col] - c0 * rows[row][col]) % 3 + 3) % 3;
      }
    }
    ++rank;
    ++pivot_col;
  }
  return rank;
}

using Matrix = DynamicMatrix<3, 1>;
using Tensor3 = std::vector<std::vector<std::vector<int>>>;  // [NA][NB][NC]

Matrix ToMatrix(const std::vector<std::vector<int>> &m) {
  Matrix out(static_cast<int>(m.size()), m.empty() ? 0 : static_cast<int>(m[0].size()));
  for (std::size_t i = 0; i < m.size(); ++i) {
    for (std::size_t j = 0; j < m[i].size(); ++j) {
      out(static_cast<int>(i), static_cast<int>(j)) = GF<3, 1>{static_cast<std::uint8_t>(m[i][j])};
    }
  }
  return out;
}

// 独立写的展平秩参考: 显式转置后对三个展平矩阵分别求秩, 次序与短路同 RankLowerBoundFlatten。
int ReferenceFlatten(const Tensor3 &t, int target) {
  const int NA = static_cast<int>(t.size());
  const int NB = NA ? static_cast<int>(t[0].size()) : 0;
  const int NC = NB ? static_cast<int>(t[0][0].size()) : 0;
  // B 位: 行 j, 列 (k, i)
  std::vector<std::vector<int>> b(NB, std::vector<int>(NC * NA));
  for (int j = 0; j < NB; ++j)
    for (int k = 0; k < NC; ++k)
      for (int i = 0; i < NA; ++i) b[j][k * NA + i] = t[i][j][k];
  const int r1 = ReferenceRank(b);
  if (r1 >= target) return r1;
  // C 位: 行 k, 列 (i, j)
  std::vector<std::vector<int>> c(NC, std::vector<int>(NA * NB));
  for (int k = 0; k < NC; ++k)
    for (int i = 0; i < NA; ++i)
      for (int j = 0; j < NB; ++j) c[k][i * NB + j] = t[i][j][k];
  const int r2 = ReferenceRank(c);
  if (r2 >= target) return r2;
  // A 位: 行 i, 列 (j, k)
  std::vector<std::vector<int>> a(NA, std::vector<int>(NB * NC));
  for (int i = 0; i < NA; ++i)
    for (int j = 0; j < NB; ++j)
      for (int k = 0; k < NC; ++k) a[i][j * NC + k] = t[i][j][k];
  const int r0 = ReferenceRank(a);
  return std::max({r0, r1, r2});
}

// 随机矩阵: kind = 0 均匀 {0,1,2}, kind = 1 低秩（两个薄矩阵之积）, kind = 2 全零
std::vector<std::vector<int>> RandomMatrix(std::mt19937_64 &rng, int n0, int n1, int kind) {
  std::vector<std::vector<int>> m(n0, std::vector<int>(n1, 0));
  std::uniform_int_distribution<int> d(0, 2);
  if (kind == 0) {
    for (auto &row : m) for (int &x : row) x = d(rng);
  } else if (kind == 1) {
    std::uniform_int_distribution<int> k(0, std::min(n0, n1));
    const int inner = k(rng);
    std::vector<std::vector<int>> a(n0, std::vector<int>(inner)), b(inner, std::vector<int>(n1));
    for (auto &row : a) for (int &x : row) x = d(rng);
    for (auto &row : b) for (int &x : row) x = d(rng);
    for (int i = 0; i < n0; ++i)
      for (int j = 0; j < n1; ++j) {
        int s = 0;
        for (int t = 0; t < inner; ++t) s += a[i][t] * b[t][j];
        m[i][j] = s % 3;
      }
  }
  return m;
}

// 随机张量: kind = 0 均匀; kind = 1 = 若干秩一项之和（张量秩 ≤ R, 展平秩有变化）
Tensor3 RandomTensor(std::mt19937_64 &rng, int NA, int NB, int NC, int kind) {
  Tensor3 t(NA, std::vector<std::vector<int>>(NB, std::vector<int>(NC, 0)));
  std::uniform_int_distribution<int> d(0, 2);
  if (kind == 0) {
    for (auto &plane : t) for (auto &row : plane) for (int &x : row) x = d(rng);
  } else {
    std::uniform_int_distribution<int> terms(0, std::min({NA, NB, NC}));
    const int R = terms(rng);
    for (int q = 0; q < R; ++q) {
      std::vector<int> a(NA), b(NB), c(NC);
      for (int &x : a) x = d(rng);
      for (int &x : b) x = d(rng);
      for (int &x : c) x = d(rng);
      for (int i = 0; i < NA; ++i)
        for (int j = 0; j < NB; ++j)
          for (int k = 0; k < NC; ++k) t[i][j][k] = (t[i][j][k] + a[i] * b[j] * c[k]) % 3;
    }
  }
  return t;
}

long g_mismatches = 0;

void Note(bool ok, const char *what) {
  if (!ok) {
    if (g_mismatches < 5) std::printf("MISMATCH in %s\n", what);
    ++g_mismatches;
  }
}

// 展平秩对拍: 形状 (NA, NB, NC) 上随机张量 × 随机阈值
template <std::size_t NA, std::size_t NB, std::size_t NC>
void CheckFlattenShape(std::mt19937_64 &rng, long trials, int *hist, int hist_size) {
  for (long t = 0; t < trials; ++t) {
    const int kind = static_cast<int>(rng() % 2);
    const Tensor3 ref = RandomTensor(rng, static_cast<int>(NA), static_cast<int>(NB),
                                     static_cast<int>(NC), kind);
    Tensor<3, 1, NA, NB, NC> ten{};
    for (std::size_t i = 0; i < NA; ++i)
      for (std::size_t j = 0; j < NB; ++j)
        for (std::size_t k = 0; k < NC; ++k)
          ten[i][j][k] = GF<3, 1>{static_cast<std::uint8_t>(ref[i][j][k])};
    std::uniform_int_distribution<int> dt(0, static_cast<int>(std::min({NA, NB, NC})) + 1);
    const int target = dt(rng);
    const int want = ReferenceFlatten(ref, target);
    const int got = RankLowerBoundFlatten<3, 1, NA, NB, NC>(ten, target);
    Note(got == want, "flatten");
    if (want >= 0 && want < hist_size) ++hist[want];
  }
}

// 退化归约剪枝的等价性: 对随机基（各维）, 比较两种扫描访问到的超空间集合。
//   全扫: 每个首项为 1 且与基无关的候选行 c;
//   极小扫: 每个关于基极小的候选行（MinimalWrtBase）。
// 超空间用规范 RREF（基向量组）作键。两种集合必须相等, 且极小候选数 = (3^(9−d) − 1) / 2。
using Vec9 = GFVec<3, 1, 9>;
using Cons9 = Constraints<3, 1, 9>;

std::vector<std::uint64_t> CanonKey(Cons9 rows) {
  const int rank = GaussJordanRREF<3, 1, 9>(&rows);
  rows.erase(rows.begin(), rows.end() - rank);
  std::vector<std::uint64_t> key;
  for (const Vec9 &v : rows) key.push_back(EncodeGFVec<3, 1, 9>(v));
  return key;
}

long CheckDegeneratePruning(std::mt19937_64 &rng) {
  long bad = 0, superspaces_full = 0, superspaces_minimal = 0;
  for (int d = 0; d <= 8; ++d) {
    const int reps = d == 0 ? 1 : 3;
    for (int rep = 0; rep < reps; ++rep) {
      // 随机基: d 个随机向量的规范 RREF
      Cons9 base;
      if (d > 0) {
        Cons9 rand;
        for (int i = 0; i < d; ++i) {
          Vec9 v{};
          for (int k = 0; k < 9; ++k) v.Set(k, GF<3, 1>{static_cast<std::uint8_t>(rng() % 3)});
          rand.push_back(v);
        }
        if (GaussJordanRREF<3, 1, 9>(&rand) != d) {
          --rep;
          continue;
        }
        base = rand;
        base.erase(base.begin(), base.end() - d);
      }
      std::vector<std::vector<std::uint64_t>> full, minimal;
      for (std::uint64_t r = 1; r < 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3 * 3; ++r) {
        const Vec9 c = DecodeGFVec<3, 1, 9>(r);
        if (c.LeadingNonzero() != GF<3, 1>::One()) continue;
        const bool minimal_row = sovereign_f3::MinimalWrtBase(base, c);
        Cons9 ext = base;
        ext.push_back(c);
        const int rank = GaussJordanRREF<3, 1, 9>(&ext);
        if (rank != d + 1) {
          if (minimal_row) {
            std::printf("PRUNING BUG: minimal candidate dependent on base (d=%d)\n", d);
            ++bad;
          }
          continue;
        }
        if (minimal_row) minimal.push_back(CanonKey(ext));
        full.push_back(CanonKey(ext));
      }
      // full 里同一个超空间会出现多次（每个张成它的候选行一次）, 所以比较的是**集合**。
      const std::set<std::vector<std::uint64_t>> full_set(full.begin(), full.end());
      const std::set<std::vector<std::uint64_t>> minimal_set(minimal.begin(), minimal.end());
      std::uint64_t pow3 = 1;
      for (int i = 0; i < 9 - d; ++i) pow3 *= 3;
      const std::size_t expect_minimal = static_cast<std::size_t>((pow3 - 1) / 2);
      const bool ok = full_set == minimal_set && minimal.size() == expect_minimal &&
                      minimal_set.size() == expect_minimal;
      if (!ok) {
        std::printf("PRUNING MISMATCH d=%d: full distinct=%zu minimal=%zu (distinct %zu) expect=%zu\n", d,
                    full_set.size(), minimal.size(), minimal_set.size(), expect_minimal);
        ++bad;
      }
      superspaces_full += static_cast<long>(full.size());
      superspaces_minimal += static_cast<long>(minimal.size());
    }
  }
  std::printf("degenerate pruning: bases checked=%d mismatches=%ld full-visits(with duplicates)=%ld minimal-visits=%ld\n",
              1 + 8 * 3, bad, superspaces_full, superspaces_minimal);
  return bad;
}

} // namespace

int main(int argc, char **argv) {
  const long trials = argc > 1 ? std::atol(argv[1]) : 200000;
  std::mt19937_64 rng(20261127);
  struct Shape { int n0, n1; };
  const Shape shapes[] = {{9, 81}, {9, 9}, {1, 1}, {5, 7}, {16, 128}, {3, 81}, {12, 4}, {2, 2}};
  long fallbacks = 0, total = 0;
  int hist[8][3][17] = {};
  for (long t = 0; t < trials; ++t) {
    const int si = static_cast<int>(rng() % 8);
    const int kind = static_cast<int>(rng() % 3);
    const auto m = RandomMatrix(rng, shapes[si].n0, shapes[si].n1, kind);
    const int ref = ReferenceRank(m);
    const Matrix mat = ToMatrix(m);
    const int got = mat.Rank();
    const int fast = sovereign_f3::RankF3Fast(
        reinterpret_cast<const std::uint8_t *>(mat.data()), mat.rows(), mat.cols());
    ++total;
    if (fast < 0) ++fallbacks;
    if (got != ref || (fast >= 0 && fast != ref)) {
      if (g_mismatches < 5) {
        std::printf("MISMATCH shape=%dx%d kind=%d ref=%d Rank()=%d fast=%d\n", shapes[si].n0,
                    shapes[si].n1, kind, ref, got, fast);
      }
      ++g_mismatches;
    }
    const int rk = ref < 17 ? ref : 16;
    ++hist[si][kind][rk];
  }
  std::printf("rank: trials=%ld mismatches=%ld fallbacks=%ld\n", total, g_mismatches, fallbacks);
  for (int si = 0; si < 8; ++si) {
    for (int kind = 0; kind < 3; ++kind) {
      std::printf("shape %2dx%3d kind %d rank histogram:", shapes[si].n0, shapes[si].n1, kind);
      for (int r = 0; r <= std::min(shapes[si].n0, shapes[si].n1); ++r) {
        std::printf(" %d:%d", r, hist[si][kind][r]);
      }
      std::printf("\n");
    }
  }
  // 展平秩对拍
  int h9[16] = {}, h234[16] = {}, h546[16] = {};
  const long m0 = g_mismatches;
  CheckFlattenShape<9, 9, 9>(rng, trials / 4, h9, 16);
  const long m1 = g_mismatches;
  CheckFlattenShape<2, 3, 4>(rng, trials / 10, h234, 16);
  const long m2 = g_mismatches;
  CheckFlattenShape<5, 4, 6>(rng, trials / 10, h546, 16);
  std::printf("flatten: (9,9,9) mismatches=%ld  (2,3,4) mismatches=%ld  (5,4,6) mismatches=%ld\n",
              m1 - m0, m2 - m1, g_mismatches - m2);
  for (int v = 0; v < 16; ++v) {
    if (h9[v] || h234[v] || h546[v]) {
      std::printf("flatten result %2d: (9,9,9) %6d   (2,3,4) %5d   (5,4,6) %5d\n", v, h9[v], h234[v], h546[v]);
    }
  }
  // 退化归约剪枝的等价性（随机基 × 候选行全枚举）
  const long pruned_bad = CheckDegeneratePruning(rng);
  std::printf("degenerate pruning mismatches=%ld\n", pruned_bad);

  // 计时: 9×9×9 随机张量上的展平秩, 以及 9×81 矩阵的秩
  {
    const Tensor3 ref = RandomTensor(rng, 9, 9, 9, 0);
    Tensor<3, 1, 9, 9, 9> ten{};
    for (int i = 0; i < 9; ++i)
      for (int j = 0; j < 9; ++j)
        for (int k = 0; k < 9; ++k)
          ten[i][j][k] = GF<3, 1>{static_cast<std::uint8_t>(ref[i][j][k])};
    const Tensor<3, 1, 9, 9, 9> &cref = ten;
    volatile int sink = 0;
    constexpr long kIters = 200000;
    auto t0 = std::chrono::steady_clock::now();
    for (long i = 0; i < kIters; ++i) sink += RankLowerBoundFlatten<3, 1, 9, 9, 9>(cref, 1000);
    auto t1 = std::chrono::steady_clock::now();
    for (long i = 0; i < kIters / 10; ++i) sink += ReferenceFlatten(ref, 1000);
    auto t2 = std::chrono::steady_clock::now();
    std::vector<std::vector<int>> mm(9, std::vector<int>(81));
    for (int i = 0; i < 9; ++i) for (int j = 0; j < 81; ++j) mm[i][j] = static_cast<int>(rng() % 3);
    for (long i = 0; i < kIters; ++i) {
      std::vector<std::uint8_t> flat(9 * 81);
      for (int a = 0; a < 9; ++a) for (int b = 0; b < 81; ++b) flat[a * 81 + b] = static_cast<std::uint8_t>(mm[a][b]);
      sink += sovereign_f3::RankF3Fast(flat.data(), 9, 81);
    }
    auto t3 = std::chrono::steady_clock::now();
    for (long i = 0; i < kIters / 10; ++i) sink += ReferenceRank(mm);
    auto t4 = std::chrono::steady_clock::now();
    std::printf("timing: flatten(9,9,9) fast %.0f ns vs reference %.0f ns; rank(9x81) fast+copy %.0f ns vs reference %.0f ns (sink %d)\n",
                std::chrono::duration<double, std::nano>(t1 - t0).count() / kIters,
                std::chrono::duration<double, std::nano>(t2 - t1).count() / (kIters / 10),
                std::chrono::duration<double, std::nano>(t3 - t2).count() / kIters,
                std::chrono::duration<double, std::nano>(t4 - t3).count() / (kIters / 10), sink);
  }
  return (g_mismatches == 0 && pruned_bad == 0) ? 0 : 1;
}
