#pragma once

// 𝔽₃ 上求秩相关的高频路径（性能专用; 语义与通用实现相同）。
//
// 为什么需要: 框架的 forced product 对每个组合都要算三个循环位的展平秩（9 × 81 的矩阵）。
//   · 通用 DynamicMatrix::Rank(): 每次调用把矩阵拷进 std::vector<std::vector<>>(堆分配)、
//     做完整的 Gauss–Jordan（求秩只需前向消元, 上面一半是多余的）、内层每个元素走带分支的
//     GF 运算;
//   · 通用 RankLowerBoundFlatten: 先做两次 CyclicTranspose（各 729 字节的分散写）, 再三次
//     构造 DynamicMatrix（各一次堆分配）。
// 实测合计每次迭代约 20 µs, 3^18 = 3.87 亿次枚举要 16 分钟。F₂ 有位打包快路径所以上游没觉得慢。
//
// 做法: 栈上平铺 uint8 数组 + 直接按跨度从张量读出展平矩阵（不做转置、不堆分配）
//      + 只消下方行 + 不归一化主元行（把主元的逆并进消元系数）+ 取模写成「比较-减法」,
//      让编译器自动向量化。
// 等价性: engineering/wang_f3ext/standalone/rank_f3_fast_check.cc 用独立写的通用实现做随机对拍
//        (求秩: 8 种形状 × 均匀/低秩/全零; 展平秩: 随机张量 × 各阈值)。
// 超出缓冲尺寸时返回 -1, 调用方回退到通用实现。

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "core/gf_vec.h"

namespace sovereign_f3 {

constexpr int kMaxRows = 16;
constexpr int kMaxCols = 128;

// rows × cols 矩阵的秩, 行跨度 stride（字节）。n0 > kMaxRows 或 n1 > kMaxCols 时返回 -1。
inline int RankF3Fast(const uint8_t *data, int n0, int n1, int stride) {
  if (n0 <= 0 || n1 <= 0) {
    return 0;
  }
  if (n0 > kMaxRows || n1 > kMaxCols) {
    return -1;
  }
  alignas(64) uint8_t rows[kMaxRows][kMaxCols];
  for (int r = 0; r < n0; ++r) {
    std::memcpy(rows[r], data + static_cast<std::size_t>(r) * stride,
                static_cast<std::size_t>(n1));
  }
  int rank = 0;
  int row = 0;
  for (int col = 0; col < n1 && row < n0; ++col) {
    int piv = -1;
    for (int r = row; r < n0; ++r) {
      if (rows[r][col] != 0) {
        piv = r;
        break;
      }
    }
    if (piv < 0) {
      continue;
    }
    if (piv != row) {
      for (int c = col; c < n1; ++c) {
        const uint8_t t = rows[row][c];
        rows[row][c] = rows[piv][c];
        rows[piv][c] = t;
      }
    }
    const uint8_t pv = rows[row][col]; // 1 或 2
    // 消去下方各行: rows[r] := rows[r] − f · rows[row]（mod 3）。
    // 不归一化主元行: f / pv = (pv == 1) ? f : 3 − f。
    for (int r = row + 1; r < n0; ++r) {
      uint8_t f = rows[r][col];
      if (f == 0) {
        continue;
      }
      if (pv == 2) {
        f = static_cast<uint8_t>(3 - f);
      }
      const uint8_t *pr = rows[row];
      uint8_t *rr = rows[r];
      if (f == 1) {
        // a − b = (a + 3 − b) mod 3, a + 3 − b ∈ [1, 5]: 最多减一次 3。
        for (int c = col; c < n1; ++c) {
          int t = rr[c] + 3 - pr[c];
          t -= (t >= 3) ? 3 : 0;
          rr[c] = static_cast<uint8_t>(t);
        }
      } else {
        // a + b ∈ [0, 4]: 最多减一次 3。
        for (int c = col; c < n1; ++c) {
          int t = rr[c] + pr[c];
          t -= (t >= 3) ? 3 : 0;
          rr[c] = static_cast<uint8_t>(t);
        }
      }
    }
    ++rank;
    ++row;
  }
  return rank;
}

// dst := dst + digit · src（mod 3, 逐字节; digit ∈ {1, 2}）。forced product 把被选中的强制行叠进张量时用,
// 与通用实现的 `tensor_t[i][j][k] + digit * r1_val` 同义, 只是写成无分支取模以便自动向量化。
inline void AddScaledRowF3(uint8_t *dst, const uint8_t *src, int n, int digit) {
  if (digit == 1) {
    for (int c = 0; c < n; ++c) {
      int t = dst[c] + src[c];
      t -= (t >= 3) ? 3 : 0;
      dst[c] = static_cast<uint8_t>(t);
    }
  } else if (digit == 2) {
    for (int c = 0; c < n; ++c) {
      int t = dst[c] + src[c] + src[c];
      t -= (t >= 3) ? 3 : 0;
      t -= (t >= 3) ? 3 : 0;
      dst[c] = static_cast<uint8_t>(t);
    }
  }
}

// 行 c 关于基（规范 RREF 的行向量组）是否「极小」: c 在基的每个主元位置上都是 0。
// 退化归约（search/rank_lower_bound_degenerate.h）用它在 F₃ 上只枚举极小候选:
//   每个与基线性无关的行 c 都对应唯一的极小代表 m = (c 减去基向量的适当组合) 归一化到首项 1,
//   且 span(基 ∪ {c}) = span(基 ∪ {m}); 不同的极小代表张成**不同**的超空间。
// 所以只扫极小候选恰好把每个 (d+1) 维超空间访问一次, 取到的 max 与全扫相同
// （区别只在平局时记录哪一个见证, 不影响证明的有效性）。
// 等价性由 engineering/wang_f3ext/standalone/rank_f3_fast_check.cc 的「极小扫描 = 全扫」一节核对。
template <class Vec> bool MinimalWrtBase(const std::vector<Vec> &base, const Vec &c) {
  for (const Vec &b : base) {
    if (c[b.LeadingNonzeroIdx()] != Vec::Field::Zero()) {
      return false;
    }
  }
  return true;
}

// 3×3 的 F₃ 群作用快路径（problems/matrix/symmetry.h 的 SymmetryGroupFq 在 P=3、M=1、N0=N1=3 时用）。
// 约束向量 = 3×3 矩阵的 9 个数位（位 i·3 + j）; 群元 = 打包的矩阵数据（base-3, 3^9 = 19683 种）。
// 与表驱动实现同义: ApplyLeft3 = L · τᵗ(V), ApplyRight3 = V · R。全部向量 × 全部群元的对拍见 README §6。
constexpr std::uint32_t kPack3x3 = 19683; // 3^9

// 打包数据 → 9 个数位
inline void DigitsOfData3(std::uint32_t d, std::uint8_t out[9]) {
  for (int k = 0; k < 9; ++k) {
    out[k] = static_cast<std::uint8_t>(d % 3);
    d /= 3;
  }
}

inline std::uint8_t Mul3(std::uint8_t a, std::uint8_t b) {
  return static_cast<std::uint8_t>(a * b % 3);
}

// W = L · τᵗ(V)
inline void ApplyLeft3(const std::uint8_t L[9], bool tr, const std::uint8_t V[9], std::uint8_t W[9]) {
  for (int i = 0; i < 3; ++i) {
    for (int j = 0; j < 3; ++j) {
      std::uint8_t s = 0;
      for (int k = 0; k < 3; ++k) {
        const std::uint8_t vkj = tr ? V[j * 3 + k] : V[k * 3 + j];
        s = static_cast<std::uint8_t>((s + L[i * 3 + k] * vkj) % 3);
      }
      W[i * 3 + j] = s;
    }
  }
}

// W = V · R
inline void ApplyRight3(const std::uint8_t V[9], const std::uint8_t R[9], std::uint8_t W[9]) {
  for (int i = 0; i < 3; ++i) {
    for (int j = 0; j < 3; ++j) {
      std::uint8_t s = 0;
      for (int k = 0; k < 3; ++k) {
        s = static_cast<std::uint8_t>((s + V[i * 3 + k] * R[k * 3 + j]) % 3);
      }
      W[i * 3 + j] = s;
    }
  }
}

// 3×3 F₃ 群作用的查表版（比上面的数位运算版更快; 语义相同）。
// 对每个矩阵数据 d（3^9 种）、每个输出行 o、每个输入三元组 x（0..26 = x₀ + 3x₁ + 9x₂）, 预先算好
//   左乘表 TabL[d][o·27 + x] = Σ_k M[o][k]·x_k（mod 3）
//   右乘表 TabR[d][o·27 + x] = Σ_k M[k][o]·x_k（mod 3）   （即 Mᵀ 的左乘表）
// 每次 Apply 只需三次「取三元组 → 查表」。
constexpr int kLinearTab = 81; // 3 行 × 27 种三元组

inline std::vector<std::array<std::uint8_t, kLinearTab>> BuildLinearTable3(bool transposed) {
  std::vector<std::array<std::uint8_t, kLinearTab>> tab(kPack3x3);
  std::uint8_t M[9];
  for (std::uint32_t d = 0; d < kPack3x3; ++d) {
    DigitsOfData3(d, M);
    for (int o = 0; o < 3; ++o) {
      for (int x = 0; x < 27; ++x) {
        const int x0 = x % 3, x1 = (x / 3) % 3, x2 = x / 9;
        int s = 0;
        if (transposed) {
          s = M[0 * 3 + o] * x0 + M[1 * 3 + o] * x1 + M[2 * 3 + o] * x2;
        } else {
          s = M[o * 3 + 0] * x0 + M[o * 3 + 1] * x1 + M[o * 3 + 2] * x2;
        }
        tab[d][static_cast<std::size_t>(o * 27 + x)] = static_cast<std::uint8_t>(s % 3);
      }
    }
  }
  return tab;
}

// 行向量 v（9 个数位）→ L · τᵗ(V), 用左乘表 tab（按 L 的矩阵数据索引）。
inline void ApplyLeftTab(const std::uint8_t *tabL, bool tr, const std::uint8_t v[9], std::uint8_t w[9]) {
  for (int j = 0; j < 3; ++j) {
    const int x = tr ? (v[j * 3 + 0] + 3 * v[j * 3 + 1] + 9 * v[j * 3 + 2])
                     : (v[0 * 3 + j] + 3 * v[1 * 3 + j] + 9 * v[2 * 3 + j]);
    w[0 * 3 + j] = tabL[0 * 27 + x];
    w[1 * 3 + j] = tabL[1 * 27 + x];
    w[2 * 3 + j] = tabL[2 * 27 + x];
  }
}

// 行向量 v → V · R, 用右乘表 tab（按 R 的矩阵数据索引）。
inline void ApplyRightTab(const std::uint8_t *tabR, const std::uint8_t v[9], std::uint8_t w[9]) {
  for (int i = 0; i < 3; ++i) {
    const int x = v[i * 3 + 0] + 3 * v[i * 3 + 1] + 9 * v[i * 3 + 2];
    w[i * 3 + 0] = tabR[0 * 27 + x];
    w[i * 3 + 1] = tabR[1 * 27 + x];
    w[i * 3 + 2] = tabR[2 * 27 + x];
  }
}

// 「列反转」Gauss–Jordan（求规范形, OrbitMap / 枚举器 / verifier 的键都靠它）, 只对 GFVec<3,1,N>。
// 与 core/math_utils.h 的 GaussJordanEliminationFq **输出逐元素相同**:
//   主元列从 N−1 往下、主元行从末行往上放、零行停在最前、主元归一化为 1、上下都消。
// 行数 > kMaxRows 或 N > kMaxCols 时返回 -1 且不改 rows（调用方回退到通用实现）。
// 等价性: engineering/wang_f3ext/standalone/rank_f3_fast_check.cc 的「规范形」一节对通用实现做随机对拍。
template <std::size_t N>
inline int GaussJordanRREF3Fast(std::vector<GFVec<3, 1, N>> *rows_ptr) {
  std::vector<GFVec<3, 1, N>> &rows = *rows_ptr;
  const int size = static_cast<int>(rows.size());
  if (size == 0 || N == 0) {
    return 0;
  }
  if (size > kMaxRows || N > kMaxCols) {
    return -1;
  }
  uint8_t buf[kMaxRows][kMaxCols];
  for (int r = 0; r < size; ++r) {
    for (std::size_t c = 0; c < N; ++c) {
      buf[r][c] = rows[static_cast<std::size_t>(r)][static_cast<int>(c)].value;
    }
  }
  const int n = static_cast<int>(N);
  int rank = 0;
  int current_row = size - 1;
  int pivot_col = n - 1;
  while (current_row >= 0 && pivot_col >= 0) {
    // 与通用实现同一个选取规则: 从 current_row 往下找第一个在主元列非零的行。
    int pivot_row = -1;
    for (int r = current_row; r >= 0; --r) {
      if (buf[r][pivot_col] != 0) {
        pivot_row = r;
        break;
      }
    }
    if (pivot_row < 0) {
      --pivot_col;
      continue;
    }
    if (pivot_row != current_row) {
      for (int c = 0; c < n; ++c) {
        const uint8_t tmp = buf[current_row][c];
        buf[current_row][c] = buf[pivot_row][c];
        buf[pivot_row][c] = tmp;
      }
    }
    // 归一化: 2⁻¹ = 2, 即把 1 与 2 互换。
    if (buf[current_row][pivot_col] != 1) {
      for (int c = 0; c < n; ++c) {
        const uint8_t x = buf[current_row][c];
        buf[current_row][c] = static_cast<uint8_t>(x == 1 ? 2 : x == 2 ? 1 : 0);
      }
    }
    // 上下都消: row_r := row_r − f · row_current（mod 3）。
    for (int r = 0; r < size; ++r) {
      const uint8_t f = buf[r][pivot_col];
      if (r == current_row || f == 0) {
        continue;
      }
      const uint8_t *pr = buf[current_row];
      uint8_t *rr = buf[r];
      if (f == 1) {
        for (int c = 0; c < n; ++c) {
          int t = rr[c] + 3 - pr[c];
          t -= (t >= 3) ? 3 : 0;
          rr[c] = static_cast<uint8_t>(t);
        }
      } else {
        for (int c = 0; c < n; ++c) {
          int t = rr[c] + pr[c];
          t -= (t >= 3) ? 3 : 0;
          rr[c] = static_cast<uint8_t>(t);
        }
      }
    }
    ++rank;
    --current_row;
    --pivot_col;
  }
  for (int r = 0; r < size; ++r) {
    for (std::size_t c = 0; c < N; ++c) {
      rows[static_cast<std::size_t>(r)].Set(static_cast<int>(c), GF<3, 1>{buf[r][c]});
    }
  }
  return rank;
}

// 行跨度 = 列数的便捷重载。
inline int RankF3Fast(const uint8_t *data, int n0, int n1) {
  return RankF3Fast(data, n0, n1, n1);
}

// 三个循环位的展平秩的最大值, 镜像 RankLowerBoundFlatten 的次序与短路:
// 先 B 位（行 j, 列 (k,i)）, 达到 target 即返回; 再 C 位（行 k, 列 (i,j)）; 最后 A 位（行 i, 列 (j,k)）。
// Tensor 的内存布局是 NA × NB × NC 的连续字节数组（每个 GF<3,1> 一个字节）。
// 尺寸超出缓冲时返回 -1, 调用方回退到通用实现。
template <std::size_t NA, std::size_t NB, std::size_t NC>
inline int RankLowerBoundFlattenF3Fast(const uint8_t *t, int target_rank) {
  constexpr std::size_t kMaxSide = std::max({NA, NB, NC});
  constexpr std::size_t kMaxFlat = std::max({NB * NC, NC * NA, NA * NB});
  if constexpr (kMaxSide > static_cast<std::size_t>(kMaxRows) ||
                kMaxFlat > static_cast<std::size_t>(kMaxCols)) {
    (void)t;
    (void)target_rank;
    return -1;
  } else {
    alignas(64) uint8_t rows[kMaxRows][kMaxCols];
    // B 位
    for (std::size_t j = 0; j < NB; ++j) {
      for (std::size_t k = 0; k < NC; ++k) {
        for (std::size_t i = 0; i < NA; ++i) {
          rows[j][k * NA + i] = t[(i * NB + j) * NC + k];
        }
      }
    }
    const int rank1 = RankF3Fast(&rows[0][0], static_cast<int>(NB),
                                 static_cast<int>(NC * NA), kMaxCols);
    if (rank1 >= target_rank) {
      return rank1;
    }
    // C 位
    for (std::size_t k = 0; k < NC; ++k) {
      for (std::size_t i = 0; i < NA; ++i) {
        for (std::size_t j = 0; j < NB; ++j) {
          rows[k][i * NB + j] = t[(i * NB + j) * NC + k];
        }
      }
    }
    const int rank2 = RankF3Fast(&rows[0][0], static_cast<int>(NC),
                                 static_cast<int>(NA * NB), kMaxCols);
    if (rank2 >= target_rank) {
      return rank2;
    }
    // A 位
    for (std::size_t i = 0; i < NA; ++i) {
      std::memcpy(rows[i], t + i * NB * NC, NB * NC);
    }
    const int rank0 = RankF3Fast(&rows[0][0], static_cast<int>(NA),
                                 static_cast<int>(NB * NC), kMaxCols);
    return std::max({rank0, rank1, rank2});
  }
}

} // namespace sovereign_f3
