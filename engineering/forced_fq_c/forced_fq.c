/* forced_fq.c — Hopcroft–Kerr 引理 2(forced product)下界的独立复算内核, 素域通用。
 *
 * 从 Wang 框架 verifier 的规格(verifier/verifier.h VerifyForcedProductProof +
 * core/rank_lower_bound_forced_product.h RankLowerBoundForcedProductA 的 q 进制支路)
 * 独立实现, 不包含其任何源码; 供 wang_cert_check_fq.py 在枚举量 q^(r2p·r1) 过大时调用。
 *
 * 输入(stdin): P projection nrows row_1 … row_nrows claim
 *   - P: 素域特征(2, 3, …); 矩阵乘法张量固定为 ⟨3,3,3⟩(na = nb = nc = 9)
 *   - projection: 0 = A 位, 1 = B 位(一次循环转置), 2 = C 位(两次)
 *   - row_i: 约束行, 基 P 打包的整数(Σ_k d_k P^k), 须在规范 RREF
 *   - claim: 证书声明的下界(仅回显核对)
 * 输出(stdout): "computed <界> bit_width <bw> iterations <num> claim_ok <0|1>"
 *
 * 算法(镜像 RankLowerBoundForcedProductA, known_lower_bound = 0):
 *   1. 按 (nb×nc) 秩给 A 切片分类; 秩 1 的切片里取极大无关组作强制积(r1), 其余非零切片入 r2p;
 *   2. bit_width = |r2p|·|r1|; 枚举 q^bit_width 个组合, 乱序访问 t ↦ (t·73074167) mod N,
 *      每个组合把 r1 行按 q 进制数字加进 r2p 切片, 取三个循环位的最优展平秩
 *      (target = 当前最小 − |r1| 时短路), 取最小;
 *   3. 返回 |r1| + 最小值。|r1| = 0 或 q^bit_width 溢出 uint64 时返回 0。
 *
 * 编译: cc -O3 -pthread -o forced_fq forced_fq.c
 */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#define NA 9
#define NB 9
#define NC 9

static int P;
static uint8_t T0[NA][NB][NC];      /* 基张量 ⟨3,3,3⟩ */
static uint8_t R1[NA][NB * NC];     /* 强制行(展平) */
static uint8_t R2P[NA][NB][NC];     /* 其余非零切片 */
static int n_r1, n_r2p, bit_width;
static __uint128_t NUM_IT;
static int64_t SHARED_MIN = INT64_MAX / 4;

static inline uint8_t fdiv(uint8_t a, uint8_t b) { /* a / b */
  int bi = 1;
  for (; (bi * b) % P != 1; ++bi) {}
  return (uint8_t)((a * bi) % P);
}

/* 展平秩(带阈值): rows[na][(nb*nc)] 个元素的矩阵, 列数 cols; 秩达到 threshold 即返回 */
static int flatten_rank(const uint8_t *mat, int nrows, int ncols, int stride, int threshold) {
  uint8_t m[NA][NB * NC];
  for (int i = 0; i < nrows; ++i) memcpy(m[i], mat + (size_t)i * stride, (size_t)ncols);
  int rank = 0;
  for (int col = 0; col < ncols && rank < nrows; ++col) {
    int piv = -1;
    for (int r = rank; r < nrows; ++r) if (m[r][col]) { piv = r; break; }
    if (piv < 0) continue;
    if (piv != rank) { uint8_t tmp[NB * NC]; memcpy(tmp, m[rank], (size_t)ncols);
                       memcpy(m[rank], m[piv], (size_t)ncols); memcpy(m[piv], tmp, (size_t)ncols); }
    if (m[rank][col] != 1) { uint8_t inv = fdiv(1, m[rank][col]);
      for (int c = col; c < ncols; ++c) m[rank][c] = (uint8_t)(m[rank][c] * inv % P); }
    for (int r = rank + 1; r < nrows; ++r) {
      if (m[r][col]) { uint8_t f = m[r][col];
        for (int c = col; c < ncols; ++c) m[r][c] = (uint8_t)((m[r][c] + P - f * m[rank][c] % P) % P); }
    }
    ++rank;
    if (rank >= threshold) return rank;
  }
  return rank;
}

/* 三个循环位的最优展平秩, target 短路(镜像 RankLowerBoundFlatten) */
static int rank_lower_bound_flatten(const uint8_t t[NA][NB][NC], int target) {
  uint8_t flat[NA][NB * NC];
  /* B 位: 行 j, 列 (k, i) */
  for (int j = 0; j < NB; ++j) for (int k = 0; k < NC; ++k) for (int i = 0; i < NA; ++i)
    flat[j][k * NA + i] = t[i][j][k];
  int r1 = flatten_rank(&flat[0][0], NB, NC * NA, NB * NC, target);
  if (r1 >= target) return r1;
  /* C 位: 行 k, 列 (i, j) */
  for (int k = 0; k < NC; ++k) for (int i = 0; i < NA; ++i) for (int j = 0; j < NB; ++j)
    flat[k][i * NB + j] = t[i][j][k];
  int r2 = flatten_rank(&flat[0][0], NC, NA * NB, NB * NC, target);
  if (r2 >= target) return r2;
  /* A 位: 行 i, 列 (j, k) */
  for (int i = 0; i < NA; ++i) for (int j = 0; j < NB; ++j) for (int k = 0; k < NC; ++k)
    flat[i][j * NC + k] = t[i][j][k];
  int r0 = flatten_rank(&flat[0][0], NA, NB * NC, NB * NC, target);
  int mx = r0; if (r1 > mx) mx = r1; if (r2 > mx) mx = r2;
  return mx;
}

typedef struct { int tid, nthreads; int64_t local_min; } targ;

static void *worker(void *arg) {
  targ *a = (targ *)arg;
  int64_t my_min = INT64_MAX / 4;
  uint8_t tt[NA][NB][NC];
  for (__uint128_t t = (__uint128_t)a->tid; t < NUM_IT; t += a->nthreads) {
    __uint128_t scrambled = (t * (__uint128_t)73074167) % NUM_IT;
    memcpy(tt, R2P, sizeof tt);
    __uint128_t v = scrambled;
    for (int b = 0; b < bit_width; ++b) {
      int d = (int)(v % (unsigned)P);
      v /= (unsigned)P;
      if (d == 0) continue;
      int r1_idx = b % n_r1, i = b / n_r1;
      for (int c = 0; c < NB * NC; ++c)
        tt[i][c / NC][c % NC] = (uint8_t)((tt[i][c / NC][c % NC] + d * R1[r1_idx][c]) % P);
    }
    int target = (my_min >= INT32_MAX / 4) ? (INT32_MAX / 4) : (int)(my_min - n_r1);
    int remaining = rank_lower_bound_flatten(tt, target);
    int64_t val = n_r1 + remaining;
    if (val < my_min) my_min = val;
  }
  a->local_min = my_min;
  return NULL;
}

static void cyclic(uint8_t src[NA][NB][NC], uint8_t dst[NA][NB][NC]) {
  /* result[j][k][i] = src[i][j][k] */
  for (int i = 0; i < NA; ++i) for (int j = 0; j < NB; ++j) for (int k = 0; k < NC; ++k)
    dst[j][k][i] = src[i][j][k];
}

static int digit(uint64_t v, int k) { for (; k; --k) v /= (uint64_t)P; return (int)(v % (uint64_t)P); }
static int leading(uint64_t v) { int ld = -1; for (int k = 0; k < NA; ++k) if (digit(v, k)) ld = k; return ld; }

int main(void) {
  int projection, nrows, claim;
  if (scanf("%d %d %d", &P, &projection, &nrows) != 3) return 2;
  uint64_t rows[NA];
  for (int i = 0; i < nrows; ++i) {
    unsigned long long r;
    if (scanf("%llu", &r) != 1) return 2;
    rows[i] = (uint64_t)r;
  }
  if (scanf("%d", &claim) != 1) return 2;

  /* 基张量 ⟨3,3,3⟩: T[i*3+j][j*3+k][k*3+i] = 1 */
  memset(T0, 0, sizeof T0);
  for (int i = 0; i < 3; ++i) for (int j = 0; j < 3; ++j) for (int k = 0; k < 3; ++k)
    T0[i * 3 + j][j * 3 + k][k * 3 + i] = 1;

  /* 约束代入(镜像 ApplyConstraintsToTensor 的 F_q 支路) */
  static uint8_t A[NA][NB][NC], B[NA][NB][NC], C[NA][NB][NC];
  memcpy(A, T0, sizeof A);
  for (int r = 0; r < nrows; ++r) {
    int pivot = leading(rows[r]);
    for (int i = 0; i < NA; ++i) {
      if (i == pivot) continue;
      int c = digit(rows[r], i);
      if (c == 0) continue;
      for (int j = 0; j < NB; ++j) for (int k = 0; k < NC; ++k)
        A[i][j][k] = (uint8_t)((A[i][j][k] + P - c * A[pivot][j][k] % P) % P);
    }
    for (int j = 0; j < NB; ++j) for (int k = 0; k < NC; ++k) A[pivot][j][k] = 0;
  }
  const uint8_t (*tensor)[NB][NC] = (const uint8_t (*)[NB][NC])A;
  if (projection == 1) { cyclic(A, B); tensor = (const uint8_t (*)[NB][NC])B; }
  else if (projection == 2) { cyclic(A, B); cyclic(B, C); tensor = (const uint8_t (*)[NB][NC])C; }

  /* 分类 */
  static uint8_t flat[NA][NB * NC], r1acc[NA][NB * NC];
  n_r1 = 0; n_r2p = 0;
  int r1_count = 0;
  for (int i = 0; i < NA; ++i) {
    for (int j = 0; j < NB; ++j) for (int k = 0; k < NC; ++k) flat[j][k] = tensor[i][j][k];
    int rk = flatten_rank(&flat[0][0], NB, NC, NB * NC, NB);
    if (rk == 0) continue;
    if (rk == 1) {
      ++r1_count;
      for (int c = 0; c < NB * NC; ++c) r1acc[n_r1][c] = flat[c / NC][c % NC];
      int newr = flatten_rank(&r1acc[0][0], n_r1 + 1, NB * NC, NB * NC, n_r1 + 1);
      if (newr == n_r1 + 1) { memcpy(R1[n_r1], r1acc[n_r1], NB * NC); ++n_r1; }
      else memcpy(R2P[n_r2p++], tensor[i], NB * NC);
    } else {
      memcpy(R2P[n_r2p++], tensor[i], NB * NC);
    }
  }
  int computed = 0;
  __uint128_t n_it = 1;
  int overflow = 0;
  bit_width = n_r2p * n_r1;
  if (r1_count > 0) {
    for (int i = 0; i < bit_width; ++i) { n_it *= (unsigned)P; if (n_it > (__uint128_t)UINT64_MAX) { overflow = 1; break; } }
    if (!overflow) {
      NUM_IT = n_it;
      int nthreads = 8;
      pthread_t th[64]; targ ta[64];
      for (int i = 0; i < nthreads; ++i) { ta[i].tid = i; ta[i].nthreads = nthreads; pthread_create(&th[i], NULL, worker, &ta[i]); }
      int64_t mn = INT64_MAX / 4;
      for (int i = 0; i < nthreads; ++i) { pthread_join(th[i], NULL); if (ta[i].local_min < mn) mn = ta[i].local_min; }
      computed = (int)mn;
    }
  }
  printf("computed %d bit_width %d iterations %llu claim_ok %d\n", computed, bit_width,
         (unsigned long long)(overflow ? 0 : (uint64_t)n_it), computed >= claim);
  return 0;
}
