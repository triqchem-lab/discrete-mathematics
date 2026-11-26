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
#include <cstdint>
#include <cstring>

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
