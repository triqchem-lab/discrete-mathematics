#pragma once

// F₃ 的 OrbitMap::Get 批量探针内核（性能专用; 语义与标量版 Get 完全相同）。
//
// 背景: Get 对一个约束组 q, 把全部 Query 元素(3×3 时 22464 个)逐个试过去。每个探针 = 把 q 的每一行
// 经群作用映过去、求规范形、在表里查。平均约 7500 个探针才命中一次。标量版每个探针约 0.55 µs,
// 一次 Get 约 4 ms——回溯搜索(dim ≤ 5)的时间几乎全在这里。
//
// 做法:
//   ① 探针成批: 16 个 Query 元素一批, 用 NEON 对 16 路同时做「群作用 + 规范形 + 标签」
//      (结构为数组: X[行][列] 是 16 个探针的数位向量)。规范形用无分支的逐列消元: 主元列从 8 到 0,
//      每列在尚未当过主元的行里取最小的非零行作主元, 归一化, 其余行全部消去。
//      规范形(RREF)由行空间唯一决定, 所以与逐个计算的结果逐位相同。
//   ② 标签预筛: 每个键(规范形行向量组)有一个 32 位标签, 与行序无关:
//         tag = Σ_rows mix32( (9 个数位各 2 位) | 主元列 << 22 ),  mix32(h) = { h *= 0x9E3779B1; h ^= h >> 15; }
//      OrbitMap::Set 首次插入一个键时把标签放进「按键维数分表」的开放寻址表; Get 先查标签表,
//      命中再回到权威的 shards_ 哈希表核对。标签表只会产生假阳性(由权威表排除), 不会产生假阴性。
//   没有 NEON 的机器走标量块内核(也享受标签表); 它是独立实现, 也是 NEON 内核的对拍参考。
// 等价性: engineering/wang_f3ext/standalone/get_simd_check.cc ——
//   NEON 块内核 vs 标量块内核逐位相同; 对真实的 OrbitMap, 批量版 Get 与原标量逻辑对同一 (q, 表)
//   返回同一首命中下标 / 界 / 见证; 对每个已存键 × 每个 Query 元素都不漏(无假阴性)。

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <vector>

#include "core/constraints.h"

#if defined(__ARM_NEON) || defined(__ARM_NEON__)
#include <arm_neon.h>
#define SOVEREIGN_F3_NEON 1
#else
#define SOVEREIGN_F3_NEON 0
#endif

namespace sovereign_f3 {

constexpr int kDim = 9;     // 约束向量长度(3×3 矩阵的数位)
constexpr int kLanes = 16;  // 一批探针数

// ------------------------------------------------------------------
// 标签
// ------------------------------------------------------------------

constexpr std::uint32_t kTagZeroSubstitute = 0x9E3779B9u;

inline std::uint32_t Mix32(std::uint32_t h) {
  h *= 0x9E3779B1u;
  h ^= h >> 15;
  return h;
}

// 一行的编码: 数位 d0..d8 各 2 位(共 18 位), 主元列放在第 22 位起。
inline std::uint32_t RowCode(const std::uint8_t *d, int pivot) {
  return static_cast<std::uint32_t>(d[0]) | (static_cast<std::uint32_t>(d[1]) << 2) |
         (static_cast<std::uint32_t>(d[2]) << 4) | (static_cast<std::uint32_t>(d[3]) << 8) |
         (static_cast<std::uint32_t>(d[4]) << 10) | (static_cast<std::uint32_t>(d[5]) << 12) |
         (static_cast<std::uint32_t>(d[6]) << 16) | (static_cast<std::uint32_t>(d[7]) << 18) |
         (static_cast<std::uint32_t>(d[8]) << 20) | (static_cast<std::uint32_t>(pivot) << 22);
}

// 键的标签: 各行编码的 mix32 之和(与行序无关); 0 用固定值代替(0 是标签表的空位标记)。
// 规范形里每行的主元 = 它的最高非零数位。
inline std::uint32_t KeyTag(const Constraints<3, 1, kDim> &key) {
  std::uint32_t tag = 0;
  for (const GFVec<3, 1, kDim> &row : key) {
    int pivot = -1;
    std::uint8_t d[kDim];
    for (int c = 0; c < kDim; ++c) {
      d[c] = row[c].value;
      if (d[c] != 0) {
        pivot = c;
      }
    }
    tag += Mix32(RowCode(d, pivot));
  }
  return tag == 0 ? kTagZeroSubstitute : tag;
}

// ------------------------------------------------------------------
// 标签表: 开放寻址, 槽 = 标签(0 = 空)。只回答「这个标签在不在」。
// ------------------------------------------------------------------
class FlatTagTable {
 public:
  // 插入一个标签(调用方保证它对应的键此前不在权威表里, 所以不会重复插入)。
  void Insert(std::uint32_t tag) {
    if (slots_.size() < 1024 || (count_ + 1) * 2 > slots_.size()) {
      Rehash(std::max<std::size_t>(1024, 4 * (count_ + 1)));
    }
    std::size_t i = tag & mask_;
    while (slots_[i] != 0) {
      i = (i + 1) & mask_;
    }
    slots_[i] = tag;
    ++count_;
  }

  inline bool Has(std::uint32_t tag) const {
    if (slots_.empty()) {
      return false;
    }
    std::size_t i = tag & mask_;
    while (slots_[i] != 0) {
      if (slots_[i] == tag) {
        return true;
      }
      i = (i + 1) & mask_;
    }
    return false;
  }

  void Clear() {
    slots_.clear();
    count_ = 0;
    mask_ = 0;
  }

 private:
  void Rehash(std::size_t want) {
    std::size_t cap = 1024;
    while (cap < want) cap <<= 1;
    std::vector<std::uint32_t> old;
    old.swap(slots_);
    slots_.assign(cap, 0);
    mask_ = cap - 1;
    for (std::uint32_t t : old) {
      if (t == 0) continue;
      std::size_t i = t & mask_;
      while (slots_[i] != 0) i = (i + 1) & mask_;
      slots_[i] = t;
    }
  }

  std::vector<std::uint32_t> slots_;
  std::size_t count_ = 0;
  std::size_t mask_ = 0;
};

// ------------------------------------------------------------------
// Query 元素的「按数位分开」布局: d[k][e] = 第 e 个元素的左乘矩阵的第 k 个数位, tr[e] = 转置标志。
// 末尾补 16 个重复元素: 最后一批不满 16 时读到的仍是合法数据(多出的道在结果里被忽略)。
// ------------------------------------------------------------------
struct QuerySoA {
  std::vector<std::uint8_t> d[kDim];
  std::vector<std::uint8_t> tr;
  int size = 0;
};

// ElemFn: void(int e, std::uint8_t *digits9, std::uint8_t *transpose)
template <class ElemFn>
inline void BuildQuerySoA(int n, ElemFn fn, QuerySoA *out) {
  out->size = n;
  for (int k = 0; k < kDim; ++k) out->d[k].resize(static_cast<std::size_t>(n) + kLanes);
  out->tr.resize(static_cast<std::size_t>(n) + kLanes);
  for (int e = 0; e < n; ++e) {
    std::uint8_t dig[kDim];
    std::uint8_t t = 0;
    fn(e, dig, &t);
    for (int k = 0; k < kDim; ++k) out->d[k][static_cast<std::size_t>(e)] = dig[k];
    out->tr[static_cast<std::size_t>(e)] = t;
  }
  for (int p = 0; p < kLanes; ++p) {
    const std::size_t src = n > 0 ? static_cast<std::size_t>(n - 1) : 0;
    for (int k = 0; k < kDim; ++k) {
      out->d[k][static_cast<std::size_t>(n) + p] = n > 0 ? out->d[k][src] : 0;
    }
    out->tr[static_cast<std::size_t>(n) + p] = n > 0 ? out->tr[src] : 0;
  }
}

// ------------------------------------------------------------------
// 块内核: 一批 16 个探针(第 e0 … e0+15 个 Query 元素作用在 q 上)
// ------------------------------------------------------------------

// 输出(按道存放):
//   row[col][c][p]   第 p 个探针的规范形里主元为 col 的那一行(没有这个主元则全 0)
//   found[col][p]    1 / 0
//   tag[p]           键的标签
// 规范形只依赖 q 的行空间(每行的 9 个数位)在左乘矩阵 L(可先转置)下的像。
struct BlockOut {
  std::uint8_t row[kDim][kDim][kLanes];
  std::uint8_t found[kDim][kLanes];
  std::uint32_t tag[kLanes];
};

// 标量块内核: 独立实现(群作用 → 完整 RREF → 按主元列归档 → 标签)。
inline void BlockKernelScalar(const std::uint8_t V[kDim][kDim], int n, const QuerySoA &soa, int e0,
                              BlockOut *out) {
  std::memset(out, 0, sizeof(*out));
  for (int p = 0; p < kLanes; ++p) {
    const int e = e0 + p;
    const int tr = soa.tr[static_cast<std::size_t>(e)] ? 1 : 0;
    std::uint8_t a[kDim][kDim];
    for (int r = 0; r < n; ++r) {
      for (int i = 0; i < 3; ++i) {
        for (int j = 0; j < 3; ++j) {
          int s = 0;
          for (int k = 0; k < 3; ++k) {
            const int l = soa.d[i * 3 + k][static_cast<std::size_t>(e)];
            const int v = tr ? V[r][j * 3 + k] : V[r][k * 3 + j];
            s += l * v;
          }
          a[r][i * 3 + j] = static_cast<std::uint8_t>(s % 3);
        }
      }
    }
    // 完整 RREF: 主元列从 8 到 0, 上、下都消
    std::uint8_t pivot_of_row[kDim];
    for (int r = 0; r < kDim; ++r) pivot_of_row[r] = 0xFF;
    for (int col = kDim - 1; col >= 0; --col) {
      int piv = -1;
      for (int r = 0; r < n; ++r) {
        if (pivot_of_row[r] == 0xFF && a[r][col] != 0) {
          piv = r;
          break;
        }
      }
      if (piv < 0) continue;
      pivot_of_row[piv] = static_cast<std::uint8_t>(col);
      const int inv = a[piv][col] == 2 ? 2 : 1;  // F₃ 里非零元的逆是它自己
      for (int c = 0; c < kDim; ++c) a[piv][c] = static_cast<std::uint8_t>(a[piv][c] * inv % 3);
      for (int r = 0; r < n; ++r) {
        if (r == piv || a[r][col] == 0) continue;
        const int f = a[r][col];
        for (int c = 0; c < kDim; ++c) {
          a[r][c] = static_cast<std::uint8_t>(((a[r][c] - f * a[piv][c]) % 3 + 3) % 3);
        }
      }
    }
    std::uint32_t tag = 0;
    for (int r = 0; r < n; ++r) {
      if (pivot_of_row[r] == 0xFF) continue;
      const int col = pivot_of_row[r];
      out->found[col][p] = 1;
      int pivot = -1;
      for (int c = 0; c < kDim; ++c) {
        out->row[col][c][p] = a[r][c];
        if (a[r][c] != 0) pivot = c;
      }
      tag += Mix32(RowCode(a[r], pivot));
    }
    out->tag[p] = tag == 0 ? kTagZeroSubstitute : tag;
  }
}

#if SOVEREIGN_F3_NEON
inline const std::uint8_t kAddTab[16] = {0, 1, 2, 1, 2, 0, 2, 0, 1, 0, 0, 0, 0, 0, 0, 0};
inline const std::uint8_t kMulTab[16] = {0, 0, 0, 0, 1, 2, 0, 2, 1, 0, 0, 0, 0, 0, 0, 0};
inline const std::uint8_t kNegTab[16] = {0, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0};
// kScale[a*3+b][3*s + l] = s·l (mod 3) 当 s ∈ {a, b}; 其余为 0
inline std::uint8_t MakeScale(int a, int b, int i) {
  const int s = i / 3, l = i % 3;
  return static_cast<std::uint8_t>((s == a || s == b) ? (s * l) % 3 : 0);
}
#define SOVEREIGN_F3_SCALE_ROW(a, b)                                                 \
  {MakeScale(a, b, 0), MakeScale(a, b, 1), MakeScale(a, b, 2), MakeScale(a, b, 3),   \
   MakeScale(a, b, 4), MakeScale(a, b, 5), MakeScale(a, b, 6), MakeScale(a, b, 7),   \
   MakeScale(a, b, 8), MakeScale(a, b, 9), MakeScale(a, b, 10), MakeScale(a, b, 11), \
   MakeScale(a, b, 12), MakeScale(a, b, 13), MakeScale(a, b, 14), MakeScale(a, b, 15)}
inline const std::uint8_t kScaleTabs[9][16] = {
    SOVEREIGN_F3_SCALE_ROW(0, 0), SOVEREIGN_F3_SCALE_ROW(0, 1), SOVEREIGN_F3_SCALE_ROW(0, 2),
    SOVEREIGN_F3_SCALE_ROW(1, 0), SOVEREIGN_F3_SCALE_ROW(1, 1), SOVEREIGN_F3_SCALE_ROW(1, 2),
    SOVEREIGN_F3_SCALE_ROW(2, 0), SOVEREIGN_F3_SCALE_ROW(2, 1), SOVEREIGN_F3_SCALE_ROW(2, 2)};
#undef SOVEREIGN_F3_SCALE_ROW

// NEON 的 vld1q 是语句表达式, 不能在文件作用域初始化向量常量, 所以放进带构造函数的目标里。
struct NeonTabs {
  uint8x16_t add, mul, neg;
  NeonTabs() : add(vld1q_u8(kAddTab)), mul(vld1q_u8(kMulTab)), neg(vld1q_u8(kNegTab)) {}
};
inline const NeonTabs kTabs;

inline uint8x16_t Add3(uint8x16_t a, uint8x16_t b) {
  return vqtbl1q_u8(kTabs.add, vaddq_u8(vaddq_u8(vshlq_n_u8(a, 1), a), b));
}
inline uint8x16_t Mul3(uint8x16_t a, uint8x16_t b) {
  return vqtbl1q_u8(kTabs.mul, vaddq_u8(vaddq_u8(vshlq_n_u8(a, 1), a), b));
}
inline uint8x16_t Sub3(uint8x16_t a, uint8x16_t b) { return Add3(a, vqtbl1q_u8(kTabs.neg, b)); }

// 8 位 ×16 道里取第 part 组(4 道)加宽成 32 位
inline uint32x4_t Quad32(const uint8x16_t v, int part) {
  const uint16x8_t w = vmovl_u8(part < 2 ? vget_low_u8(v) : vget_high_u8(v));
  return vmovl_u16((part & 1) == 0 ? vget_low_u16(w) : vget_high_u16(w));
}

// 把规范形的一行(主元列 col, 9 个数位在 P[0..8], 高于 col 的为 0)累进标签:
// code = (d0..d8 各 2 位) | col << 22; tag += found ? mix32(code) : 0
inline void AccumTag(const uint8x16_t *P, int col, const uint8x16_t found01, uint32x4_t *tag) {
  const uint8x16_t v0 = vorrq_u8(vorrq_u8(P[0], vshlq_n_u8(P[1], 2)), vshlq_n_u8(P[2], 4));
  const uint8x16_t v1 = vorrq_u8(vorrq_u8(P[3], vshlq_n_u8(P[4], 2)), vshlq_n_u8(P[5], 4));
  const uint8x16_t v2 = vorrq_u8(vorrq_u8(P[6], vshlq_n_u8(P[7], 2)), vshlq_n_u8(P[8], 4));
  const uint32x4_t colv = vdupq_n_u32(static_cast<std::uint32_t>(col) << 22);
  for (int part = 0; part < 4; ++part) {
    uint32x4_t code = Quad32(v0, part);
    code = vorrq_u32(code, vshlq_n_u32(Quad32(v1, part), 8));
    code = vorrq_u32(code, vshlq_n_u32(Quad32(v2, part), 16));
    code = vorrq_u32(code, colv);
    uint32x4_t mix = vmulq_n_u32(code, 0x9E3779B1u);
    mix = veorq_u32(mix, vshrq_n_u32(mix, 15));
    // found01 是 0/1: 先扩成全 1 / 全 0 的掩码(0 − found), 再按位与。
    const uint32x4_t fmask = vsubq_u32(vdupq_n_u32(0), Quad32(found01, part));
    tag[part] = vaddq_u32(tag[part], vandq_u32(mix, fmask));
  }
}

// NEON 块内核。
inline void BlockKernelNeon(const std::uint8_t V[kDim][kDim], int n, const QuerySoA &soa, int e0,
                            BlockOut *out) {
  const uint8x16_t zero = vdupq_n_u8(0);
  const uint8x16_t one = vdupq_n_u8(1);
  const uint8x16_t trmask = vceqq_u8(vld1q_u8(&soa.tr[static_cast<std::size_t>(e0)]), one);
  uint8x16_t L[3][3];
  for (int i = 0; i < 3; ++i) {
    for (int k = 0; k < 3; ++k) L[i][k] = vld1q_u8(&soa.d[i * 3 + k][static_cast<std::size_t>(e0)]);
  }
  // 群作用: X[r][i][j] = Σ_k L[i][k] · (tr ? V[r][j][k] : V[r][k][j])
  uint8x16_t X[kDim][kDim];
  for (int r = 0; r < n; ++r) {
    for (int i = 0; i < 3; ++i) {
      for (int j = 0; j < 3; ++j) {
        uint8x16_t acc = zero;
        for (int k = 0; k < 3; ++k) {
          const int na = V[r][k * 3 + j];  // 不转置: V[k][j]
          const int tr_b = V[r][j * 3 + k];  // 转置: V[j][k]
          const uint8x16_t sel =
              vbslq_u8(trmask, vdupq_n_u8(static_cast<std::uint8_t>(tr_b)),
                       vdupq_n_u8(static_cast<std::uint8_t>(na)));
          const uint8x16_t idx = vaddq_u8(vaddq_u8(vshlq_n_u8(sel, 1), sel), L[i][k]);
          acc = Add3(acc, vqtbl1q_u8(vld1q_u8(kScaleTabs[na * 3 + tr_b]), idx));
        }
        X[r][i * 3 + j] = acc;
      }
    }
  }
  // 逐列消元: 记下每行当主元时的列 pc[r](0xFF = 还没当过)。
  uint8x16_t pc[kDim];
  for (int r = 0; r < kDim; ++r) pc[r] = vdupq_n_u8(0xFF);
  for (int col = kDim - 1; col >= 0; --col) {
    uint8x16_t P[kDim];
    for (int c = 0; c < kDim; ++c) P[c] = zero;
    uint8x16_t selflag[kDim];
    uint8x16_t found = zero;
    const uint8x16_t colv = vdupq_n_u8(static_cast<std::uint8_t>(col));
    for (int r = 0; r < n; ++r) {
      const uint8x16_t nz = vmvnq_u8(vceqq_u8(X[r][col], zero));
      const uint8x16_t used = vceqq_u8(pc[r], vdupq_n_u8(0xFF));
      const uint8x16_t m = vbicq_u8(vandq_u8(nz, used), found);  // 可当主元 且 本列尚未选出
      for (int c = 0; c <= col; ++c) P[c] = vbslq_u8(m, X[r][c], P[c]);
      found = vorrq_u8(found, m);
      selflag[r] = m;
      pc[r] = vbslq_u8(m, colv, pc[r]);
    }
    // 归一化: F₃ 里非零元的逆是它自己; 归一化后的主元行要写回 X(输出行取自 X)。
    for (int c = 0; c <= col; ++c) P[c] = Mul3(P[c], P[col]);
    for (int r = 0; r < n; ++r) {
      for (int c = 0; c <= col; ++c) X[r][c] = vbslq_u8(selflag[r], P[c], X[r][c]);
    }
    // 其余行消去本列(主元行自身 f = 0, 不变)。
    for (int r = 0; r < n; ++r) {
      const uint8x16_t f = vbslq_u8(selflag[r], zero, X[r][col]);
      for (int c = 0; c <= col; ++c) X[r][c] = Sub3(X[r][c], Mul3(f, P[c]));
    }
  }
  // 按主元列归档: row[col][c] = OR_r ( X[r][c] 当 pc[r] == col ), found[col] = 有这样的行。
  uint32x4_t tag[4] = {vdupq_n_u32(0), vdupq_n_u32(0), vdupq_n_u32(0), vdupq_n_u32(0)};
  for (int col = 0; col < kDim; ++col) {
    uint8x16_t P[kDim];
    uint8x16_t f01 = zero;
    for (int c = 0; c < kDim; ++c) P[c] = zero;
    for (int r = 0; r < n; ++r) {
      const uint8x16_t hit = vceqq_u8(pc[r], vdupq_n_u8(static_cast<std::uint8_t>(col)));
      f01 = vorrq_u8(f01, vandq_u8(hit, one));
      for (int c = 0; c < kDim; ++c) P[c] = vorrq_u8(P[c], vandq_u8(X[r][c], hit));
    }
    AccumTag(P, col, f01, tag);
    for (int c = 0; c < kDim; ++c) vst1q_u8(&out->row[col][c][0], P[c]);
    vst1q_u8(&out->found[col][0], f01);
  }
  alignas(16) std::uint32_t t[kLanes];
  for (int part = 0; part < 4; ++part) vst1q_u32(&t[4 * part], tag[part]);
  for (int p = 0; p < kLanes; ++p) out->tag[p] = t[p] == 0 ? kTagZeroSubstitute : t[p];
}

inline void BlockKernel(const std::uint8_t V[kDim][kDim], int n, const QuerySoA &soa, int e0,
                        BlockOut *out) {
  BlockKernelNeon(V, n, soa, e0, out);
}
#else
inline void BlockKernel(const std::uint8_t V[kDim][kDim], int n, const QuerySoA &soa, int e0,
                        BlockOut *out) {
  BlockKernelScalar(V, n, soa, e0, out);
}
#endif

// ------------------------------------------------------------------
// 整个 Get 的探针循环(与标量版同样的次序: 按下标从小到大, 返回第一个命中)。
//   Lookup: int(const Constraints<3,1,9>& key, Store *store) → 权威表里的界(≥ 0)或 −1。
// 返回: 首命中的界与见证; 全部未命中返回 −1。
// ------------------------------------------------------------------
template <class Lookup, class Store>
int ProbeAll(const Constraints<3, 1, kDim> &q, const QuerySoA &soa,
             const std::vector<FlatTagTable> &flat_by_k, Lookup lookup, int *hit_query,
             Store *hit_store) {
  // q 可以有超过 9 行(回溯搜索把多条额外行加在基上, 允许线性相关)。像的行空间只依赖 q 的跨度,
  // 所以先把 q 约化成行空间的规范基(至多 9 行): 结果与见证都不受影响, 内核只需处理 n <= 9。
  Constraints<3, 1, kDim> basis = q;
  const int n = GaussJordanRREF<3, 1, kDim>(&basis);
  basis.erase(basis.begin(), basis.end() - n);
  std::uint8_t V[kDim][kDim];
  for (int r = 0; r < n; ++r) {
    for (int c = 0; c < kDim; ++c) V[r][c] = basis[static_cast<std::size_t>(r)][c].value;
  }
  BlockOut out;
  Constraints<3, 1, kDim> key;
  for (int e0 = 0; e0 < soa.size; e0 += kLanes) {
    BlockKernel(V, n, soa, e0, &out);
    const int m = std::min(kLanes, soa.size - e0);
    for (int p = 0; p < m; ++p) {
      int k = 0;
      for (int col = 0; col < kDim; ++col) k += out.found[col][p];
      if (!flat_by_k[static_cast<std::size_t>(k)].Has(out.tag[p])) continue;  // 标签不在 ⇒ 键不在
      key.clear();
      for (int col = 0; col < kDim; ++col) {
        if (!out.found[col][p]) continue;
        GFVec<3, 1, kDim> row;
        for (int c = 0; c < kDim; ++c) {
          row.Set(c, GF<3, 1>{out.row[col][c][p]});
        }
        key.push_back(row);
      }
      Store st{};
      const int rank = lookup(key, &st);
      if (rank >= 0) {
        *hit_query = e0 + p;
        *hit_store = st;
        return rank;
      }
    }
  }
  return -1;
}

} // namespace sovereign_f3
