/* bt_fq.c — 回溯下界证明(backtracking proof)的独立重放内核, 素域通用。
 *
 * 从 Wang 框架 verifier 的规格(verifier/backtracking_verifier.h 与 search/rank_lower_bound_backtracking.h
 * 的 Search 记录格式)独立实现, 不包含其任何源码; 逐条镜像 wang_cert_check.py /
 * wang_cert_check_fq.py 里 make_backtracking_verifier 的断言。
 *
 * 输入(stdin):
 *   P NA
 *   nbase b_1 … b_nbase            基约束行(规范 RREF; 基 P 打包整数 Σ_k d_k P^k)
 *   claim                          证书声明的下界
 *   nrec                           证明记录数
 *   size mask query store          × nrec(DFS 前序; size = 该记录处的 dfs 深度, mask = 被选中的路径行)
 *   nmap                           轨道表条目数
 *   k r_1 … r_k rank               × nmap(某轨道代表的规范形行向量组 + 它已核对的下界)
 * 输出(stdout): "bt ok <0|1> nodes <n> leaves <k> reason <…>"
 *
 * 重放语义(与 Python 版逐条一致):
 *   dfs(idx_max, 深度 d):
 *     取下一条记录 pi(没有 → 失败); 记录深度 s; d ≤ s(否则失败);
 *     d == s: mask 不得选到路径之外; 必须选最新路径项; d > 0;
 *             extended = 基 + mask 选中的 dfs 行; 用见证 (query, store) 把它映到规范形;
 *             规范形必须在轨道表里; claim ≤ popcount(mask) + 表中的界(否则失败); pi++;
 *     d <  s: d < claim − 1(否则失败: 分支未在 L−1 深度内闭合); 对 i = 0..idx_max 递归。
 *   结束后 pi 必须 == nrec。
 *
 * 群作用: 矩阵 = 基 P 打包的 9 个数位, 位 (i*3+j) = (i,j); query = {l, transpose}(l | transpose<<16),
 *         store = R; 规范形 = RREF(store.ApplyInverse(R, query.Apply(query, extended)))。
 *         这里直接写: t = v 或 vᵀ; w = l·t; w·R⁻¹; RREF。
 *
 * 编译: cc -O2 -o bt_fq bt_fq.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* NMAX ≥ 32: claim ≤ 32 ⟹ DFS 深度 ≤ 31, 路径与 extended 行组都按这个上界开。
 * 2026-11-27 实测: 取 16 时, 对 claim > 17 的证书(上游 F₂ ⟨3,3,3⟩, dim ≤ 4)重放会写越界并 abort。 */
#define NMAX 40

static int P, NA;

static uint32_t powp(int place) { uint32_t p = 1; for (int t = 0; t < place; ++t) p *= (uint32_t)P; return p; }
static int dig(uint64_t v, int place) { return (int)((v / (uint64_t)powp(place)) % (uint64_t)P); }
static int lead(uint64_t v) { int ld = -1; for (int k = 0; k < NA; ++k) if (dig(v, k)) ld = k; return ld; }
static int modinv(int a) { int bi = 1; for (; (bi * a) % P != 1; ++bi) {} return bi; }

/* ---------- 3×3 矩阵(打包数据)的 (i,j) 元 ---------- */
static int md(uint32_t e, int i, int j) { return (int)((e / powp(i * 3 + j)) % (uint32_t)P); }

/* ---------- 行 → 9 个数位 / 9 个数位 → 行 ---------- */
static void to_digits(uint64_t v, uint8_t d[NMAX]) { for (int k = 0; k < NA; ++k) d[k] = (uint8_t)dig(v, k); }
static uint64_t from_digits(const uint8_t d[NMAX]) {
  uint64_t v = 0, p = 1;
  for (int k = 0; k < NA; ++k) { v += (uint64_t)d[k] * p; p *= (uint64_t)P; }
  return v;
}

/* R 的逆(3×3), 伴随矩阵法; 不可逆返回 0 */
static int inv3(uint32_t r, int out[9]) {
  int m[9];
  for (int i = 0; i < 3; ++i) for (int j = 0; j < 3; ++j) m[i * 3 + j] = md(r, i, j);
  int det = m[0] * (m[4] * m[8] - m[5] * m[7]) - m[1] * (m[3] * m[8] - m[5] * m[6]) + m[2] * (m[3] * m[7] - m[4] * m[6]);
  det = ((det % P) + P) % P;
  if (det == 0) return 0;
  const int di = modinv(det);
  out[0] = di * (m[4] * m[8] - m[5] * m[7]); out[1] = di * (m[2] * m[7] - m[1] * m[8]); out[2] = di * (m[1] * m[5] - m[2] * m[4]);
  out[3] = di * (m[5] * m[6] - m[3] * m[8]); out[4] = di * (m[0] * m[8] - m[2] * m[6]); out[5] = di * (m[2] * m[3] - m[0] * m[5]);
  out[6] = di * (m[3] * m[7] - m[4] * m[6]); out[7] = di * (m[1] * m[6] - m[0] * m[7]); out[8] = di * (m[0] * m[4] - m[1] * m[3]);
  for (int i = 0; i < 9; ++i) out[i] = ((out[i] % P) + P) % P;
  return 1;
}

/* l 可逆 ⟺ 伴随矩阵法能求逆 */
static int is_gl(uint32_t e) { int inv[9]; return inv3(e, inv); }

/* 见证映射: t = v 或 vᵀ; w = l·t; w·R⁻¹。l、R 不可逆或 transpose 非法时返回 0 */
static int apply_witness(uint32_t q, uint32_t s, const uint8_t v[NMAX], uint8_t w[NMAX]) {
  const uint32_t l = q & 0xFFFFu, tr = (q >> 16) & 0xFFFFu;
  if (tr > 1) return 0;
  int rinv[9];
  if (!inv3(s, rinv) || !is_gl(l)) return 0;
  uint8_t t[9];
  for (int i = 0; i < 3; ++i) for (int j = 0; j < 3; ++j) t[i * 3 + j] = tr ? v[j * 3 + i] : v[i * 3 + j];
  int u[9];
  for (int i = 0; i < 3; ++i) for (int j = 0; j < 3; ++j) {
    int acc = 0;
    for (int k = 0; k < 3; ++k) acc += md(l, i, k) * t[k * 3 + j];
    u[i * 3 + j] = acc % P;
  }
  for (int i = 0; i < 3; ++i) for (int j = 0; j < 3; ++j) {
    int acc = 0;
    for (int k = 0; k < 3; ++k) acc += u[i * 3 + k] * rinv[k * 3 + j];
    w[i * 3 + j] = (uint8_t)(acc % P);
  }
  return 1;
}

/* 规范形: RREF(主元从最高列起, 上下全消, 主元归一), 去零行, 行按数值升序。返回秩 */
static int canon(const uint8_t rows[][NMAX], int n, uint64_t key[NMAX]) {
  uint8_t a[NMAX][NMAX];
  for (int r = 0; r < n; ++r) memcpy(a[r], rows[r], (size_t)NA);
  int rank = 0;
  for (int col = NA - 1; col >= 0; --col) {
    int piv = -1;
    for (int r = rank; r < n; ++r) if (a[r][col]) { piv = r; break; }
    if (piv < 0) continue;
    if (piv != rank) { uint8_t tmp[NMAX]; memcpy(tmp, a[rank], (size_t)NA); memcpy(a[rank], a[piv], (size_t)NA); memcpy(a[piv], tmp, (size_t)NA); }
    const int inv = modinv(a[rank][col]);
    for (int c = 0; c < NA; ++c) a[rank][c] = (uint8_t)(a[rank][c] * inv % P);
    for (int r = 0; r < n; ++r) {
      if (r == rank || !a[r][col]) continue;
      const int f = a[r][col];
      for (int c = 0; c < NA; ++c) a[r][c] = (uint8_t)(((a[r][c] - f * a[rank][c]) % P + P) % P);
    }
    ++rank;
  }
  for (int r = 0; r < rank; ++r) key[r] = from_digits(a[r]);
  /* 升序(数值大的行主元列更高) */
  for (int i = 1; i < rank; ++i) { uint64_t x = key[i]; int j = i - 1; while (j >= 0 && key[j] > x) { key[j + 1] = key[j]; --j; } key[j + 1] = x; }
  return rank;
}

/* ---------- 轨道表: 开放寻址 ---------- */
typedef struct { int k; uint64_t key[NMAX]; int rank; int used; } Entry;
static Entry *g_tab; static unsigned g_mask; static int g_power;

static uint64_t hash_key(int k, const uint64_t key[NMAX]) {
  uint64_t h = 1469598103934665603ULL ^ (uint64_t)k;
  for (int i = 0; i < k; ++i) { h ^= key[i] + 0x9e3779b97f4a7c15ULL * (uint64_t)(i + 1); h *= 1099511628211ULL; }
  return h;
}
static void map_insert(int k, const uint64_t key[NMAX], int rank) {
  uint64_t h = hash_key(k, key) & g_mask;
  while (g_tab[h].used) {
    if (g_tab[h].k == k && memcmp(g_tab[h].key, key, sizeof(uint64_t) * (size_t)k) == 0) { g_tab[h].rank = rank; return; }
    h = (h + 1) & g_mask;
  }
  g_tab[h].used = 1; g_tab[h].k = k; g_tab[h].rank = rank; memcpy(g_tab[h].key, key, sizeof(uint64_t) * (size_t)k);
}
static const Entry *map_find(int k, const uint64_t key[NMAX]) {
  uint64_t h = hash_key(k, key) & g_mask;
  while (g_tab[h].used) {
    if (g_tab[h].k == k && memcmp(g_tab[h].key, key, sizeof(uint64_t) * (size_t)k) == 0) return &g_tab[h];
    h = (h + 1) & g_mask;
  }
  return NULL;
}

/* ---------- 重放 ---------- */
static int nbase, nrec, claim, g_pi, g_fail;
static uint64_t base_rows[NMAX], minimal[100000];
static int nminimal;
/* 记录按 nrec 动态分配(2026-11-27 之前是 1<<22 的静态数组: 上游 F₂ ⟨3,3,3⟩ dim 4 的证明超过 419 万条) */
#define NREC_MAX (1u << 28)
static int *rec_size, *rec_mask;
static uint32_t *rec_q, *rec_s;
static int path_idx[NMAX];           /* 路径上各层选的极小约束下标 */
static uint64_t ext_rows[NMAX];
static unsigned long long g_nodes;

static int popcount32(unsigned x) { int c = 0; while (x) { x &= x - 1; ++c; } return c; }

static const char *g_reason;

static void dfs(int idx_max, int depth) {
  if (g_fail) return;
  ++g_nodes;
  if (g_pi >= nrec) { g_fail = 1; g_reason = "trace exhausted"; return; }
  const int s = rec_size[g_pi];
  if (depth > s) { g_fail = 1; g_reason = "depth exceeds record"; return; }
  if (depth == s) {
    const unsigned mask = (unsigned)rec_mask[g_pi];
    if (!(s > 0)) { g_fail = 1; g_reason = "record depth is zero"; return; }
    if (mask & ~((1u << s) - 1u)) { g_fail = 1; g_reason = "mask selects outside the path"; return; }
    if (!(mask & (1u << (s - 1)))) { g_fail = 1; g_reason = "mask must select the latest path item"; return; }
    int ne = 0;
    for (int r = 0; r < nbase; ++r) ext_rows[ne++] = base_rows[r];
    for (int i = 0; i < s; ++i) if ((mask >> i) & 1u) ext_rows[ne++] = minimal[path_idx[i]];
    if (!(ne > nbase)) { g_fail = 1; g_reason = "no added constraint"; return; }
    uint8_t rows[NMAX][NMAX], w[NMAX][NMAX];
    for (int r = 0; r < ne; ++r) to_digits(ext_rows[r], rows[r]);
    for (int r = 0; r < ne; ++r) if (!apply_witness(rec_q[g_pi], rec_s[g_pi], rows[r], w[r])) { g_fail = 1; g_reason = "witness not in the symmetry group"; return; }
    uint64_t key[NMAX];
    const int rank = canon(w, ne, key);
    const Entry *e = map_find(rank, key);
    if (!e) { g_fail = 1; g_reason = "leaf canonical not in map"; return; }
    const int proved = popcount32(mask) + e->rank;
    if (!(claim <= proved)) { g_fail = 1; g_reason = "claim > proved"; return; }
    ++g_pi;
    return;
  }
  if (!(depth < claim - 1)) { g_fail = 1; g_reason = "branch not closed within L-1"; return; }
  for (int i = 0; i <= idx_max; ++i) {
    path_idx[depth] = i;
    dfs(i, depth + 1);
    if (g_fail) return;
  }
}

int main(void) {
  int p_, na_;
  if (scanf("%d %d", &p_, &na_) != 2) return 2;
  P = p_; NA = na_;
  if (NA < 1 || NA > NMAX || P < 2) { printf("bt ok 0 nodes 0 leaves 0 reason bad P/NA\n"); return 0; }
  if (scanf("%d", &nbase) != 1) return 2;
  for (int r = 0; r < nbase; ++r) { unsigned long long x; if (scanf("%llu", &x) != 1) return 2; base_rows[r] = x; }
  if (scanf("%d", &claim) != 1) return 2;
  if (scanf("%d", &nrec) != 1) return 2;
  if (nrec < 0 || (unsigned)nrec > NREC_MAX) return 2;
  rec_size = malloc(sizeof(int) * (size_t)(nrec ? nrec : 1));
  rec_mask = malloc(sizeof(int) * (size_t)(nrec ? nrec : 1));
  rec_q = malloc(sizeof(uint32_t) * (size_t)(nrec ? nrec : 1));
  rec_s = malloc(sizeof(uint32_t) * (size_t)(nrec ? nrec : 1));
  if (!rec_size || !rec_mask || !rec_q || !rec_s) return 2;
  for (int i = 0; i < nrec; ++i) {
    unsigned long long m, q, s;
    if (scanf("%d %llu %llu %llu", &rec_size[i], &m, &q, &s) != 4) return 2;
    rec_mask[i] = (int)m; rec_q[i] = (uint32_t)q; rec_s[i] = (uint32_t)s;
  }
  int nmap;
  if (scanf("%d", &nmap) != 1) return 2;
  g_power = 1; while ((1 << g_power) < 2 * nmap + 2) ++g_power;
  g_mask = (unsigned)((1u << g_power) - 1);
  g_tab = calloc((size_t)(g_mask + 1), sizeof(Entry));
  if (!g_tab) return 2;
  for (int i = 0; i < nmap; ++i) {
    int k, rank;
    if (scanf("%d", &k) != 1) return 2;
    uint64_t key[NMAX];
    for (int r = 0; r < k; ++r) { unsigned long long x; if (scanf("%llu", &x) != 1) return 2; key[r] = x; }
    if (scanf("%d", &rank) != 1) return 2;
    for (int a = 1; a < k; ++a) { uint64_t x = key[a]; int b = a - 1; while (b >= 0 && key[b] > x) { key[b + 1] = key[b]; --b; } key[b + 1] = x; }
    map_insert(k, key, rank);
  }
  /* 极小约束: 首数字为 1(最高非零位), 且在基的每个主元位为 0; 升序 */
  int pivots[NMAX], np = 0;
  for (int r = 0; r < nbase; ++r) if (base_rows[r]) pivots[np++] = lead(base_rows[r]);
  uint64_t total = 1; for (int k = 0; k < NA; ++k) total *= (uint64_t)P;
  nminimal = 0;
  for (uint64_t v = 1; v < total; ++v) {
    const int ld = lead(v);
    if (dig(v, ld) != 1) continue;
    int ok = 1;
    for (int t = 0; t < np; ++t) if (dig(v, pivots[t])) { ok = 0; break; }
    if (ok) minimal[nminimal++] = v;
  }
  g_pi = 0; g_fail = 0; g_nodes = 0; g_reason = "";
  if (!(0 < claim && claim <= 32)) { g_fail = 1; g_reason = "claim out of range"; }
  else if (nminimal == 0) { g_fail = 1; g_reason = "minimal set empty"; }
  else if (nrec == 0) { g_fail = 1; g_reason = "empty trace"; }
  else {
    dfs(nminimal - 1, 0);
    if (!g_fail && g_pi != nrec) { g_fail = 1; g_reason = "trace length mismatch"; }
  }
  printf("bt ok %d nodes %llu leaves %d reason %s\n", g_fail ? 0 : 1, g_nodes, g_pi, g_reason);
  return 0;
}
