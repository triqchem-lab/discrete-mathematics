// orbit_lookup.cc —— 「子空间 → 证书界」查表 + 一个首因子配置的容量约束检查。
//
// 用途: 「容量–剖面」探针（PROVEN §二十三）。容量约束: 若 ⟨3,3,3⟩ 有 r 项分解, 首因子 a_t ∈ A,
//   W ⊆ A 是子空间, N(W) = #{t : a_t ∈ W}, 则把第一变元限制到 V ⊆ W^⊥ 会消掉首因子落在 W 里的项,
//   剩下 r − N(W) 项给出 T|_{V×B×C} 的分解 ⟹ L(V) ≤ r − N(W)。取 V = W^⊥ 最强:
//       N(W) + L(W^⊥) ≤ r。
//   证书里一个条目的约束行张成的正是某个 W, 所以给定 W 的一组基, 规范化成证书的约束行,
//   在 OrbitMap 里查一次就得到 L(W^⊥)。OrbitMap（上游 search/orbit_map.h）: Store 侧 = 右乘 GL₃
//   (11,232 个), Query 侧 = 左乘 GL₃ × 转置 (22,464 个); 装入全部 736 个轨道约 830 万个表项。
//
// 命令（从标准输入逐行读）:
//   S <seed> <K>                 自检: 每个证书条目 c 取 K 个随机群像 g·c (g = query∘store), 规范化后
//                                Get 必须命中同一个界, 且由见证还原出 c。输出 SELFTEST <条目数> <像数> <失败数>
//   Q <id> <k> <k 个 9 位数字串>  查询: k 行约束 = W 的基; 第 p 个字符是坐标 p (= i·3 + j, 行主序)。
//                                输出 R <id> <界> <证书位置> <query_elem(l|t<<16)> <store_elem(R 的数据)>
//   C <r> <n> <n 个 9 位数字串>   检查 n 个首因子在 r 项分解下的全部容量约束:
//                                D <dim> <候选数> <违规数> (dim = 1..8); Z <候选总数> <违规总数> <超出之和>
//   E <n> <g1> … <g8> <n 行>      类型无关的放宽检查: 违规 = N(W) > g[dim W]。ED 各维候选数; Z <违规数> <超出>
//   G <n> <n 行>                  配置矩阵零空间码的重量分布（探索用）: GW w=1..9 的码字直线数; G <秩> <罚项>;
//                                GP 各点参与的罚项; H <违规超平面数> <超出之和> <最大占用>（按 r = 19）
//
// 候选子空间的枚举（C 与 E 共用, 子集法, 可证明完备）: 只需检查「自己里面的点张成自己」的 W
//   （否则取其点的张成 S ⊆ W, N 相同而 L(S^⊥) ≥ L(W^⊥), 约束只会更紧）。
//   thr(d) = r − max{L : 余维 d} + 1。违规的 W 满足 N(W) ≥ thr(dim W) =: t, 而它的点张成 W,
//   所以其中有 t 个点张成恰为 W（取 W 的一组基, 再用 W 里其余的点补到 t 个）。
//   ⚠ 首版用「自顶向下取超平面 + 按阈值剪枝」, 对任意 (n, r) 并不安全（祖先维数更大、阈值也更大,
//   中间节点可能被剪掉）; 随机配置下靠鸽巢原理碰巧完备。已废弃, 换成子集法后全部数字逐项不变。
//
// 验证证据（2026-11-28, 驱动 engineering/wang_capacity_probe.py）:
//   · 自检: 736 条目 × 4..6 个随机群像, 0 失败;
//   · 见证的独立复核: Python 用自己写的矩阵乘法重放 v ↦ (L·τᵗ(v))·R⁻¹, 60/60 落回证书条目的子空间;
//   · 与纯 Python 的子集枚举互证: 两个随机 19 点配置, 候选数与违规多重集逐项相同;
//   · 强验证: Laderman 真实 23 项分解的 23 个首因子在 r = 23 下检查 645 个候选子空间, 零违规
//     （真实分解必然满足容量约束）。
//
// 诚实边界: 「证书界」是下界, 不是受限制张量的真实秩。一个配置零违规只说明它满足
//   「按证书界写出的」容量约束, 不说明满足真实秩给出的（更强的）容量约束。
//
// 编译: bash engineering/wang_f3ext/build.sh 3 lookup /tmp/wang-f3/orbit_lookup
//   （等价于 build.sh 的 clang++ 一行, 主文件换成本文件）
// 运行: /tmp/wang-f3/orbit_lookup engineering/wang_f3ext/certs/matrix_q03_n333_v1.pb.txt < 命令
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <map>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>

#include "core/certificate.pb.h"
#include "core/constraints.h"
#include "core/proto_io.h"
#include "problems/chosen_problem.h"
#include "search/orbit_map.h"

using Problem = ChosenProblem;
using Cons = Constraints<Problem::kP, Problem::kM, Problem::kNA>;
using Hash = ConstraintsHash<Problem::kP, Problem::kM, Problem::kNA>;

// 规范化 = 列反转的 RREF (证书里的约束行就是这个形状); 零行停在开头, 去掉。
static Cons Canonical(Cons c) {
  const int rank = GaussJordanRREF<Problem::kP, Problem::kM, Problem::kNA>(&c);
  c.erase(c.begin(), c.begin() + (static_cast<int>(c.size()) - rank));
  return c;
}

static std::string Show(const Cons &c) {
  std::string s;
  for (const auto &row : c) {
    s += ' ';
    for (int k = 0; k < Problem::kNA; ++k) {
      s += static_cast<char>('0' + row[k].value);
    }
  }
  return s;
}

using Vec = typename Problem::SymmetryGroup::Vec;

// 群作用逐行作用在单个行向量上; 这里作用到整个约束集合。
template <class F> static Cons ApplyRows(F f, const Cons &c) {
  Cons out;
  for (const Vec &v : c) {
    out.push_back(f(v));
  }
  return out;
}

// ---------- F₃ 小向量（探针自己的实现, 不经框架的线性代数） ----------
using V9 = std::array<uint8_t, 9>;

// 最左主元的 RREF, 零行剔除。
static void RrefInPlace(std::vector<V9> &m) {
  int r = 0;
  for (int c = 0; c < 9 && r < static_cast<int>(m.size()); ++c) {
    int p = -1;
    for (int i = r; i < static_cast<int>(m.size()); ++i) {
      if (m[i][c]) { p = i; break; }
    }
    if (p < 0) continue;
    std::swap(m[r], m[p]);
    if (m[r][c] == 2) {
      for (int k = c; k < 9; ++k) m[r][k] = static_cast<uint8_t>(m[r][k] * 2 % 3);
    }
    for (int i = 0; i < static_cast<int>(m.size()); ++i) {
      if (i == r || !m[i][c]) continue;
      const int f = m[i][c];
      for (int k = c; k < 9; ++k) m[i][k] = static_cast<uint8_t>((m[i][k] + (3 - f) * m[r][k]) % 3);
    }
    ++r;
  }
  m.resize(r);
}

// 点在 RREF 基下的坐标; 不在张成里时返回 false。
static bool InSpan(const V9 &p, const std::vector<V9> &basis) {
  V9 v = p;
  for (int i = 0; i < static_cast<int>(basis.size()); ++i) {
    int c = 0;
    while (c < 9 && basis[i][c] == 0) ++c;
    if (v[c] == 0) continue;
    const int f = v[c];
    for (int k = c; k < 9; ++k) v[k] = static_cast<uint8_t>((v[k] + (3 - f) * basis[i][k]) % 3);
  }
  for (int k = 0; k < 9; ++k) if (v[k]) return false;
  return true;
}

static Vec RowToVec(const V9 &r) {
  Vec v;
  for (int k = 0; k < 9; ++k) v.Set(k, GF<Problem::kP, Problem::kM>(r[k]));
  return v;
}

static std::string KeyOf(const std::vector<V9> &basis) {
  std::string key;
  for (const V9 &b : basis) {
    for (int k = 0; k < 9; ++k) key.push_back(static_cast<char>('0' + b[k]));
  }
  return key;
}

// 候选子空间: 一个 span-of-points 的基, 以及落在其中的点
struct Cand {
  std::vector<V9> basis;
  std::vector<int> idx;
};

// 子集法枚举: 对每个 d, 所有 thr[d] 元子集中张成维数恰为 d 的, 取其张成 W（去重）。
static std::map<std::string, Cand> EnumerateSubsets(const std::vector<V9> &points, const int *thr) {
  const int n = static_cast<int>(points.size());
  std::map<std::string, Cand> out;
  for (int d = 1; d <= 8; ++d) {
    const int t = thr[d];
    if (t < 1 || t > n) continue;
    std::vector<int> comb(static_cast<size_t>(t));
    std::iota(comb.begin(), comb.end(), 0);
    while (true) {
      std::vector<V9> rows;
      rows.reserve(static_cast<size_t>(t));
      for (int i = 0; i < t; ++i) rows.push_back(points[static_cast<size_t>(comb[i])]);
      RrefInPlace(rows);
      if (static_cast<int>(rows.size()) == d) {
        const std::string key = KeyOf(rows);
        if (!out.count(key)) {
          Cand c;
          c.basis = rows;
          for (int j = 0; j < n; ++j) {
            if (InSpan(points[static_cast<size_t>(j)], rows)) c.idx.push_back(j);
          }
          out[key] = c;
        }
      }
      int i = t - 1;
      while (i >= 0 && comb[i] == n - t + i) --i;
      if (i < 0) break;
      ++comb[i];
      for (int k = i + 1; k < t; ++k) comb[k] = comb[k - 1] + 1;
    }
  }
  return out;
}

int main(int argc, char **argv) {
  if (argc < 2) {
    std::fprintf(stderr, "usage: %s <cert.pb.txt>  (commands on stdin)\n", argv[0]);
    return 2;
  }
  pb::Certificate certificate = ReadProtoFromFile<pb::Certificate>(argv[1]);
  CHECK_EQ(certificate.characteristic(), Problem::kP);
  CHECK_EQ(certificate.extension_degree(), Problem::kM);
  CHECK_EQ(certificate.na(), Problem::kNA);
  const typename Problem::SymmetryGroup group;
  OrbitMap<Problem> map(&group);
  std::unordered_map<Cons, int, Hash> position;
  std::vector<Cons> canon;
  int max_bound_at_codim[10];
  for (int d = 0; d < 10; ++d) max_bound_at_codim[d] = -1;
  int without_bound = 0;
  for (const pb::ConstrainedTensor &rt : certificate.constrained_tensors()) {
    Cons c = ConstraintsFromBytes<Problem::kP, Problem::kM, Problem::kNA>(rt.constraints());
    CHECK(Canonical(c) == c) << "certificate constraints not canonical, index " << rt.index();
    if (!rt.has_rank_lower_bound()) {
      without_bound++;
      continue;
    }
    map.Set(c, rt.rank_lower_bound());
    position.emplace(c, static_cast<int>(canon.size()));
    max_bound_at_codim[static_cast<int>(c.size())] =
        std::max(max_bound_at_codim[static_cast<int>(c.size())], rt.rank_lower_bound());
    canon.push_back(c);
  }
  for (int d = 0; d < 10; ++d) CHECK_GE(max_bound_at_codim[d], 0) << "no orbit at codim " << d;
  for (int d = 1; d < 10; ++d) {
    CHECK_LE(max_bound_at_codim[d], max_bound_at_codim[d - 1]) << "max L must be non-increasing in dim";
  }
  std::fprintf(stderr, "loaded %d orbits with bounds (%d without), query size %d, store size %d\n",
               static_cast<int>(canon.size()), without_bound, group.query.Size(), group.store.Size());

  // 带见证的查询（Q 与自检用）: 位置由见证独立还原
  //   c = store.ApplyInverse(store_elem, query.Apply(query_elem, q))
  auto lookup = [&](const Cons &q, int *bound_out, int *pos_out, uint32_t *qe_out, uint32_t *se_out) {
    typename OrbitMap<Problem>::QueryElem qe;
    typename OrbitMap<Problem>::StoreElem se;
    const int bound = map.Get(q, &qe, &se);
    if (bound_out) *bound_out = bound;
    if (qe_out) *qe_out = static_cast<uint32_t>(qe);
    if (se_out) *se_out = static_cast<uint32_t>(se);
    if (bound < 0) {
      if (pos_out) *pos_out = -1;
      return;
    }
    const Cons back = Canonical(ApplyRows(
        [&](Vec v) { return group.store.ApplyInverse(se, group.query.Apply(qe, v)); }, q));
    const auto it = position.find(back);
    CHECK(it != position.end()) << "witness maps back to a subspace that is not in the certificate:" << Show(back);
    CHECK_EQ(canon[it->second].size(), q.size());
    if (pos_out) *pos_out = it->second;
  };

  // C: 检查一个首因子配置（全部容量约束）
  auto evaluate = [&](int r, const std::vector<V9> &points) {
    int thr[10];
    for (int d = 0; d < 10; ++d) thr[d] = r - max_bound_at_codim[d] + 1;
    const std::map<std::string, Cand> cands = EnumerateSubsets(points, thr);
    long ncand = 0, nviol = 0, excess_sum = 0, printed = 0;
    std::vector<std::array<long, 3>> per_dim(10, {0, 0, 0});
    std::vector<std::string> viol_lines;
    for (const auto &kv : cands) {
      const Cand &c = kv.second;
      const int d = static_cast<int>(c.basis.size());
      const int N = static_cast<int>(c.idx.size());
      Cons q;
      for (const V9 &b : c.basis) q.push_back(RowToVec(b));
      const int bound = map.Get(Canonical(q));
      ++ncand;
      ++per_dim[d][0];
      if (N + bound > r) {
        ++nviol;
        ++per_dim[d][1];
        excess_sum += N + bound - r;
        if (printed < 2000) {
          viol_lines.push_back("V " + std::to_string(d) + " " + std::to_string(N) + " " +
                              std::to_string(bound) + " -1");
        }
        ++printed;
      }
    }
    for (int d = 1; d <= 8; ++d) {
      std::printf("D %d %ld %ld\n", d, per_dim[d][0], per_dim[d][1]);
    }
    for (const std::string &s : viol_lines) std::printf("%s\n", s.c_str());
    std::printf("Z %ld %ld %ld\n", ncand, nviol, excess_sum);
  };

  // E: 类型无关的放宽检查
  auto evaluate_caps = [&](const std::vector<V9> &points, const int *g) {
    const int n = static_cast<int>(points.size());
    int thr[10];
    for (int d = 1; d <= 8; ++d) thr[d] = g[d] + 1;
    const std::map<std::string, Cand> cands = EnumerateSubsets(points, thr);
    long nviol = 0, excess = 0;
    std::vector<long> per_dim(10, 0);
    for (const auto &kv : cands) {
      const Cand &c = kv.second;
      const int d = static_cast<int>(c.basis.size());
      const int N = static_cast<int>(c.idx.size());
      per_dim[d]++;
      if (N > g[d]) {
        nviol++;
        excess += N - g[d];
      }
    }
    (void)n;
    std::printf("ED");
    for (int d = 1; d <= 8; ++d) std::printf(" %ld", per_dim[d]);
    std::printf("\nZ %ld %ld\n", nviol, excess);
  };

  std::string line;
  long answered = 0;
  while (std::getline(std::cin, line)) {
    std::istringstream in(line);
    std::string cmd;
    if (!(in >> cmd) || cmd.empty() || cmd[0] == '#') continue;
    if (cmd == "S") {
      unsigned long seed = 0;
      int K = 0;
      in >> seed >> K;
      std::mt19937_64 rng(seed);
      long images = 0, failures = 0;
      const int qs = group.query.Size(), ss = group.store.Size();
      for (int i = 0; i < static_cast<int>(canon.size()); ++i) {
        for (int k = 0; k < K; ++k) {
          const auto qe = group.query.At(static_cast<int>(rng() % static_cast<unsigned long>(qs)));
          const auto se = group.store.At(static_cast<int>(rng() % static_cast<unsigned long>(ss)));
          Cons img = Canonical(ApplyRows(
              [&](Vec v) { return group.query.Apply(qe, group.store.Apply(se, v)); }, canon[i]));
          int bound = -1, pos = -1;
          uint32_t wq = 0, ws = 0;
          lookup(img, &bound, &pos, &wq, &ws);
          images++;
          if (bound != certificate.constrained_tensors(i).rank_lower_bound() || pos != i) {
            failures++;
            std::fprintf(stderr, "SELFTEST FAIL at certificate position %d: bound %d pos %d\n", i, bound, pos);
          }
        }
      }
      std::printf("SELFTEST %d %ld %ld\n", static_cast<int>(canon.size()), images, failures);
      std::fflush(stdout);
      continue;
    }
    if (cmd == "E") {
      // E <n> <g1> … <g8> <n 个 9 位数字串>
      int nn = 0;
      in >> nn;
      int g[9];
      for (int d = 1; d <= 8; ++d) in >> g[d];
      std::vector<V9> rows;
      for (int rr = 0; rr < nn; ++rr) {
        std::string tok;
        in >> tok;
        CHECK_EQ(static_cast<int>(tok.size()), 9) << "row must have 9 digits";
        V9 row{};
        for (int p = 0; p < 9; ++p) {
          CHECK('0' <= tok[p] && tok[p] < '0' + Problem::kP) << "digit out of range";
          row[p] = static_cast<uint8_t>(tok[p] - '0');
        }
        rows.push_back(row);
      }
      evaluate_caps(rows, g);
      std::fflush(stdout);
      continue;
    }
    if (cmd == "Q" || cmd == "C" || cmd == "G") {
      const bool is_config = (cmd == "C");
      const bool is_girth = (cmd == "G");
      int r = 0;
      if (is_config) in >> r;
      if (is_girth) r = 19;  // G 的超平面项按 r = 19 计
      long long id = 0;
      int k = 0;
      if (!is_config && !is_girth) in >> id;
      in >> k;
      std::vector<V9> rows;
      for (int rr = 0; rr < k; ++rr) {
        std::string tok;
        in >> tok;
        CHECK_EQ(static_cast<int>(tok.size()), 9) << "row must have 9 digits";
        V9 row{};
        for (int p = 0; p < 9; ++p) {
          CHECK('0' <= tok[p] && tok[p] < '0' + Problem::kP) << "digit out of range";
          row[p] = static_cast<uint8_t>(tok[p] - '0');
        }
        rows.push_back(row);
      }
      if (is_config) {
        evaluate(r, rows);
        std::fflush(stdout);
        continue;
      }
      if (is_girth) {
        // G: 配置矩阵 (9 × n) 的零空间码的重量分布。
        const int n = k;
        std::vector<std::vector<uint8_t>> M(9, std::vector<uint8_t>(static_cast<size_t>(n)));
        for (int c = 0; c < 9; ++c) {
          for (int j = 0; j < n; ++j) M[c][j] = rows[j][c];
        }
        std::vector<int> piv;
        int rr = 0;
        for (int c = 0; c < n && rr < 9; ++c) {
          int p = -1;
          for (int i = rr; i < 9; ++i) {
            if (M[i][c]) { p = i; break; }
          }
          if (p < 0) continue;
          std::swap(M[rr], M[p]);
          if (M[rr][c] == 2) {
            for (int k2 = c; k2 < n; ++k2) M[rr][k2] = static_cast<uint8_t>(M[rr][k2] * 2 % 3);
          }
          for (int i = 0; i < 9; ++i) {
            if (i == rr || !M[i][c]) continue;
            const int f = M[i][c];
            for (int k2 = c; k2 < n; ++k2) M[i][k2] = static_cast<uint8_t>((M[i][k2] + (3 - f) * M[rr][k2]) % 3);
          }
          piv.push_back(c);
          ++rr;
        }
        std::vector<int> free_cols;
        for (int c = 0; c < n; ++c) {
          if (std::find(piv.begin(), piv.end(), c) == piv.end()) free_cols.push_back(c);
        }
        const int nf = static_cast<int>(free_cols.size());
        std::vector<std::vector<uint8_t>> vb(static_cast<size_t>(nf), std::vector<uint8_t>(static_cast<size_t>(n)));
        for (int fi = 0; fi < nf; ++fi) {
          vb[fi][free_cols[fi]] = 1;
          for (size_t i = 0; i < piv.size(); ++i) {
            vb[fi][piv[i]] = static_cast<uint8_t>((3 - M[i][free_cols[fi]]) % 3);
          }
        }
        long counts[32] = {0};
        long total = 1;
        for (int i = 0; i < nf; ++i) total *= 3;
        std::vector<uint8_t> cw(static_cast<size_t>(n));
        std::vector<long> part(static_cast<size_t>(n), 0);
        for (long code = 1; code < total; ++code) {
          long x = code;
          int firstval = 0;
          std::fill(cw.begin(), cw.end(), 0);
          for (int i = 0; i < nf; ++i) {
            const int a = static_cast<int>(x % 3);
            x /= 3;
            if (a && !firstval) firstval = a;
            if (!a) continue;
            for (int j = 0; j < n; ++j) cw[j] = static_cast<uint8_t>((cw[j] + a * vb[i][j]) % 3);
          }
          if (firstval != 1) continue;
          int w = 0;
          for (int j = 0; j < n; ++j) w += (cw[j] != 0);
          if (w < 32) counts[w]++;
          if (w <= 8) {
            for (int j = 0; j < n; ++j) if (cw[j]) part[j] += 9 - w;
          }
        }
        long penalty = 0;
        for (int w = 1; w < 9; ++w) penalty += (9 - w) * counts[w];
        std::printf("GW");
        for (int w = 1; w <= 9; ++w) std::printf(" %ld", counts[w]);
        std::printf("\nG %d %ld\n", rr, penalty);
        std::printf("GP");
        for (int j = 0; j < n; ++j) std::printf(" %ld", part[j]);
        std::printf("\n");
        // 超平面项: 对每条法向量直线 u, N(u) = 落在 ker u 里的点数; W = ker u 的零化子是直线 ⟨u⟩,
        // 证书界 L = 3·rank(u)（u 看成 3×3 矩阵）, 所以 N ≤ r − 3·rank(u)。
        {
          long hviol = 0, hexcess = 0, maxocc = 0;
          const long ulim = 19683;
          std::vector<uint8_t> u(9);
          for (long code = 1; code < ulim; ++code) {
            long x = code;
            int first = -1;
            for (int k2 = 0; k2 < 9; ++k2) {
              u[k2] = static_cast<uint8_t>(x % 3);
              x /= 3;
              if (u[k2] && first < 0) first = k2;
            }
            if (u[first] != 1) continue;
            int occ = 0;
            for (int j = 0; j < n; ++j) {
              int s = 0;
              for (int k2 = 0; k2 < 9; ++k2) s += u[k2] * rows[j][k2];
              if (s % 3 == 0) occ++;
            }
            if (occ > maxocc) maxocc = occ;
            int rk = 0;
            {
              int mm[3][3];
              for (int i = 0; i < 3; ++i) {
                for (int j = 0; j < 3; ++j) mm[i][j] = u[3 * i + j];
              }
              for (int c = 0; c < 3; ++c) {
                int p = -1;
                for (int i = rk; i < 3; ++i) {
                  if (mm[i][c]) { p = i; break; }
                }
                if (p < 0) continue;
                for (int j = 0; j < 3; ++j) std::swap(mm[rk][j], mm[p][j]);
                const int iv = mm[rk][c] == 1 ? 1 : 2;
                for (int j = 0; j < 3; ++j) mm[rk][j] = static_cast<uint8_t>(mm[rk][j] * iv % 3);
                for (int i = 0; i < 3; ++i) {
                  if (i == rk || !mm[i][c]) continue;
                  const int f = mm[i][c];
                  for (int j = 0; j < 3; ++j) mm[i][j] = static_cast<uint8_t>((mm[i][j] + (3 - f) * mm[rk][j]) % 3);
                }
                rk++;
              }
            }
            const int cap = r - 3 * rk;
            if (occ > cap) {
              hviol++;
              hexcess += occ - cap;
            }
          }
          std::printf("H %ld %ld %ld\n", hviol, hexcess, maxocc);
        }
        std::fflush(stdout);
        continue;
      }
      Cons q;
      for (const V9 &row : rows) q.push_back(RowToVec(row));
      const Cons cq = Canonical(q);
      int bound = -1, pos = -1;
      uint32_t wq = 0, ws = 0;
      lookup(cq, &bound, &pos, &wq, &ws);
      std::printf("R %lld %d %d %u %u\n", id, bound, pos, wq, ws);
      answered++;
      if (answered % 500 == 0) std::fflush(stdout);
      continue;
    }
    std::fprintf(stderr, "unknown command: %s\n", cmd.c_str());
    return 2;
  }
  std::fflush(stdout);
  return 0;
}
