#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""M25 / M26 / M27 oracle: 容量引理 / 剖面算术 / 秩预算 的数值核对（零第三方依赖）

对应的 Agda 件（都在 src/Sovereign/Algebra/LinearAlgebra/）:
  · TensorRankCapacityGF3.agda（M25）: rank-drops（限制后恒零的项可以全部丢掉）与容量不等式 N + L ≤ r
  · TensorRankProfileGF3.agda（M26）: 秩剖面的算术（Σ 秩 = n³ ⟺ n₂ + 2·n₃ = n³ − r）
  · TensorRankBudgetGF3.agda（M27）: 秩预算 —— 首因子由 N 个秩一片块拼成 ⟹ n³ ≤ N

先算后验纪律: 每条判据都打印「前提成立数」, 并断言它 > 0; 每条都有负对照。
  判据甲 (M25): 随机分解上, 把子集 S 的项丢掉后, 余和在 V = {x : S 的首因子在 x 处全为 0} 上逐点等于 T;
                负对照: 丢掉一个不在 S 里、且在某个 x 处非零的项, 余和必须与 T 不一致。
  判据乙 (M25): 真实分解上的容量不等式 N + L ≤ r —— Laderman 23 项、W = 过某个首因子的直线、L = 3·rank(a₀)。
  判据丙 (M26): (r, n) 取 (19,3)、(23,3)、(22,3)、(7,2)、(8,2): Σ 秩 = n³ 的剖面恰是参数化
                n₃ = k, n₂ = n³ − r − 2k, n₁ = r − n³ + k（0 ≤ k ≤ ⌊(n³ − r)/2⌋）给出的那些, 一个不多一个不少;
                r = 19, n = 3 时恰是 (11,8,0) (12,6,1) (13,4,2) (14,2,3) (15,0,4)。
  判据丁 (M27): 分割展平 P[(i,a,b),(i'',i',k')] = Σ_t A_t[i,i''] B_t[a,b] C_t[i',k'] 恰是 δ(i,i')·δ(a,i'')·δ(b,k')
                （Laderman 27×27、Strassen 8×8、n³ 项标准分解）; P = X·Yᵀ, X = L_t[i,α]·B_t[a,b], Y = R_t[i'',α]·C_t[i',k'];
                N = Σ_t rank(A_t) ≥ n³, Strassen 与标准分解取等; 负对照: 把预算写成 n³ ≤ N − 1 必须失败。
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_rank3_witness_gf3 as O          # LAD 表, gf3_rank, check_scheme
import oracle_tensor_rank_gf3 as S            # Strassen 的 ALPHA / BETA / C


def full_rank_factor(A):
    """A = L·Rᵀ: L = A 的主元列 (n×r), Rᵀ = RREF 的非零行 (r×n)"""
    n = len(A)
    rows = [list(r) for r in A]
    pivcols = []
    r0 = 0
    for c in range(n):
        p = next((i for i in range(r0, n) if rows[i][c] % 3), None)
        if p is None:
            continue
        rows[r0], rows[p] = rows[p], rows[r0]
        iv = {1: 1, 2: 2}[rows[r0][c] % 3]
        rows[r0] = [(x * iv) % 3 for x in rows[r0]]
        for i in range(n):
            if i != r0 and rows[i][c] % 3:
                f = rows[i][c]
                rows[i] = [(x - f * y) % 3 for x, y in zip(rows[i], rows[r0])]
        pivcols.append(c)
        r0 += 1
    L = [[A[i][c] % 3 for c in pivcols] for i in range(n)]
    return L, rows[:r0]


def mm3(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) % 3 for j in range(len(B[0]))] for i in range(len(A))]


def mat(col, n):
    """行主序 9 元组 → n×n 矩阵"""
    return [[col[n * i + j] % 3 for j in range(n)] for i in range(n)]


def laderman():
    """Laderman 23 项: 首因子 / 第二因子 / 第三因子, 都是 n×n 矩阵"""
    n = 3
    U, V, W = O.LAD['U'], O.LAD['V'], O.LAD['W']
    k = len(U[0])
    A = [mat([U[x][t] for x in range(n * n)], n) for t in range(k)]
    B = [mat([V[x][t] for x in range(n * n)], n) for t in range(k)]
    C = [mat([W[x][t] for x in range(n * n)], n) for t in range(k)]
    return A, B, C, n


def strassen():
    n = 2
    Aa, Bb, Cc = S.m22_tables()[:3]
    A = [mat(Aa[t], n) for t in range(7)]
    B = [mat(Bb[t], n) for t in range(7)]
    C = [mat(Cc[t], n) for t in range(7)]
    return A, B, C, n


def schoolbook(n):
    """n³ 项标准分解: A_t = E_ij, B_t = E_jk, C_t = E_ik（输出位置是 (i,k)）"""
    E = lambda i, j: [[1 if (a, b) == (i, j) else 0 for b in range(n)] for a in range(n)]
    A, B, C = [], [], []
    for i in range(n):
        for j in range(n):
            for k in range(n):
                A.append(E(i, j))
                B.append(E(j, k))
                C.append(E(i, k))
    return A, B, C, n


def is_decomposition(A, B, C, n):
    """Σ_t A_t ⊗ B_t ⊗ C_t 是 ⟨n,n,n⟩: 对全部 (i,j,k,i',k') Σ_t A_t[i,j] B_t[j,k] C_t[i',k'] = δ(i,i')δ(k,k')"""
    bad = 0
    for i, j, k, ip, kp in itertools.product(range(n), repeat=5):
        v = sum(A[t][i][j] * B[t][j][k] * C[t][ip][kp] for t in range(len(A))) % 3
        if v != (1 if (i == ip and k == kp) else 0):
            bad += 1
    return bad


# ---------------------------------------------------------------------------
# M25: 容量引理
# ---------------------------------------------------------------------------
def check_capacity_random(trials=200):
    """判据甲: 随机分解 + 随机子集 S; 丢掉 S 后余和在 V 上等于 T; 负对照丢错项必须出错"""
    import random
    rng = random.Random(20261128)
    ok = tried = wrong = 0
    for _ in range(trials):
        nx, ny, nz, r = rng.randint(1, 5), rng.randint(1, 4), rng.randint(1, 4), rng.randint(1, 6)
        a = [[rng.randrange(3) for _ in range(nx)] for _ in range(r)]
        b = [[rng.randrange(3) for _ in range(ny)] for _ in range(r)]
        c = [[rng.randrange(3) for _ in range(nz)] for _ in range(r)]
        S_ = [t for t in range(r) if rng.random() < 0.4]                 # 落在 W 里的项
        rest = [t for t in range(r) if t not in S_]
        xstar = rng.randrange(nx)                                        # 造一个公共零点, 保证 V 非空
        for t in S_:
            a[t][xstar] = 0
        V = [x for x in range(nx) if all(a[t][x] == 0 for t in S_)]     # ⊆ W^⊥ 的点
        assert xstar in V
        T = lambda x, y, z: sum(a[t][x] * b[t][y] * c[t][z] for t in range(r)) % 3
        R = lambda x, y, z: sum(a[t][x] * b[t][y] * c[t][z] for t in rest) % 3
        if all(R(x, y, z) == T(x, y, z) for x in V for y in range(ny) for z in range(nz)):
            ok += 1
        tried += 1
        # 负对照: 从 rest 里挑一个在 V 上某处非零的项, 把它也丢掉
        cand = [t for t in rest if any(a[t][x] != 0 for x in V)]
        if cand:
            t0 = cand[0]
            rest2 = [t for t in rest if t != t0]
            R2 = lambda x, y, z: sum(a[t][x] * b[t][y] * c[t][z] for t in rest2) % 3
            if any(R2(x, y, z) != T(x, y, z) for x in V for y in range(ny) for z in range(nz)):
                wrong += 1
    return tried, ok, wrong


def check_capacity_line(A, B, C, n):
    """判据乙: 对真实分解的每个首因子 a₀, 取 W = 过 a₀ 的直线, V = {x : a₀(x) = 0};
       N = 首因子落在 W 里的项数, L = 3·rank(a₀) (n = 3) 或 2·rank(a₀) (n = 2);
       核对 (i) N + L ≤ r; (ii) 丢掉那 N 项后余和在 V 上等于 T。"""
    r = len(A)
    cases = 0
    viol = 0
    mism = 0
    for t0 in range(r):
        a0 = [A[t0][i][j] for i in range(n) for j in range(n)]
        if not any(a0):
            continue                                                     # 零首因子: 直线没定义, 跳过
        cls = []                                                         # 首因子落在 span{a₀} 里的项: a_t = λ·a₀
        for t in range(r):
            at = [A[t][i][j] for i in range(n) for j in range(n)]
            nz = [k for k, v in enumerate(a0) if v]
            lam = at[nz[0]] * {1: 1, 2: 2}[a0[nz[0]]] % 3
            if all(at[k] == lam * a0[k] % 3 for k in range(n * n)):
                cls.append(t)
        N = len(cls)
        L = n * O.gf3_rank(A[t0])
        cases += 1
        if N + L > r:
            viol += 1
        V = [(i, j) for i in range(n) for j in range(n) if A[t0][i][j] == 0]
        rest = [t for t in range(r) if t not in cls]
        for (i, j), (jq, k), (ip, kp) in itertools.product(V, itertools.product(range(n), repeat=2), itertools.product(range(n), repeat=2)):
            Rv = sum(A[t][i][j] * B[t][jq][k] * C[t][ip][kp] for t in rest) % 3
            if Rv != (1 if (i == ip and j == jq and k == kp) else 0):     # 首版漏了 j = jq 这个条件
                mism += 1
    return cases, viol, mism


# ---------------------------------------------------------------------------
# M26: 剖面算术
# ---------------------------------------------------------------------------
def profiles_by_bruteforce(r, n):
    """全部 (n₁, n₂, n₃): 项数恰为 r, Σ 秩 = n³"""
    return sorted((n1, n2, n3) for n1 in range(r + 1) for n2 in range(r + 1 - n1)
                  for n3 in range(r + 1 - n1 - n2) if n1 + n2 + n3 == r and n1 + 2 * n2 + 3 * n3 == n ** 3)


def profiles_by_formula(r, n):
    """参数化: n₃ = k, n₂ = n³ − r − 2k, n₁ = 2r − n³ + k; k 从 max(0, n³ − 2r) 到 ⌊(n³ − r)/2⌋"""
    out = []
    for k in range(0, r + 1):
        n2, n1 = n ** 3 - r - 2 * k, 2 * r - n ** 3 + k
        if n1 >= 0 and n2 >= 0:
            out.append((n1, n2, k))
    return sorted(out)


def check_profiles():
    expect = {(19, 3): [(11, 8, 0), (12, 6, 1), (13, 4, 2), (14, 2, 3), (15, 0, 4)],
              (23, 3): [(19, 4, 0), (20, 2, 1), (21, 0, 2)],
              (22, 3): [(17, 5, 0), (18, 3, 1), (19, 1, 2)],
              (7, 2): [(6, 1, 0)],
              (8, 2): [(8, 0, 0)],
              (9, 2): []}                                                   # r > n³: 没有剖面（对照: 空集）
    nonempty = 0
    for (r, n), want in sorted(expect.items()):
        got = profiles_by_bruteforce(r, n)
        assert got == want == profiles_by_formula(r, n), ((r, n), got, want, profiles_by_formula(r, n))
        nonempty += len(got) > 0
    # 负对照: Σ 秩 = n³ + 1 的剖面不在上面的表里 (Δ = 1 的剖面, r = 19, n = 3)
    d1 = sorted((n1, n2, n3) for n1 in range(20) for n2 in range(20 - n1) for n3 in range(20 - n1 - n2)
                if n1 + n2 + n3 == 19 and n1 + 2 * n2 + 3 * n3 == 28)
    assert d1 and not set(d1) & set(expect[(19, 3)])
    return nonempty, len(expect), len(d1)


# ---------------------------------------------------------------------------
# M27: 秩预算
# ---------------------------------------------------------------------------
def check_budget(A, B, C, n):
    """判据丁: 分割展平是恒等置换; P = X·Yᵀ; N = Σ rank ≥ n³。返回 (失配数, N, n³)"""
    r = len(A)
    bad = 0
    for i, a, b, i2, i1, k1 in itertools.product(range(n), repeat=6):
        P = sum(A[t][i][i2] * B[t][a][b] * C[t][i1][k1] for t in range(r)) % 3
        want = 1 if (i == i1 and a == i2 and b == k1) else 0
        if P != want:
            bad += 1
    # P = X·Yᵀ
    facs = [full_rank_factor(A[t]) for t in range(r)]
    for i, a, b, i2, i1, k1 in itertools.product(range(n), repeat=6):
        v = 0
        for t in range(r):
            L, Rt = facs[t]
            for al in range(len(Rt)):
                X = L[i][al] * B[t][a][b] % 3
                Y = Rt[al][i2] * C[t][i1][k1] % 3
                v = (v + X * Y) % 3
        if v != (1 if (i == i1 and a == i2 and b == k1) else 0):
            bad += 1
    N = sum(O.gf3_rank(A[t]) for t in range(r))
    return bad, N, n ** 3


def main():
    # ---- M25 ----
    tried, ok, wrong = check_capacity_random()
    print("M25 容量引理(随机分解, 丢掉落在 W 里的项后余和 = T): %d/%d (随机分解 %d 个); "
          "负对照(丢掉一个不在 W 里、在 V 上非零的项 → 余和 ≠ T) %d 次" % (ok, tried, tried, wrong))
    A, B, C, n = laderman()
    assert is_decomposition(A, B, C, n) == 0, "Laderman 表不是分解"
    cases, viol, mism = check_capacity_line(A, B, C, n)
    print("M25 容量不等式(Laderman 23 项, W = 过首因子 a₀ 的直线, L = 3·rank a₀): 不同的非零首因子 %d 个, "
          "违反 N + L ≤ r 的 %d 个, 丢项后余和与 T 不一致的 (v,y,z) %d 个" % (cases, viol, mism))
    A2, B2, C2, n2 = strassen()
    assert is_decomposition(A2, B2, C2, n2) == 0, "Strassen 表不是分解"
    cases2, viol2, mism2 = check_capacity_line(A2, B2, C2, n2)
    print("M25 同上(Strassen 7 项, 2×2, L = 2·rank a₀): %d / %d / %d" % (cases2, viol2, mism2))
    # ---- M26 ----
    nonempty, total, d1 = check_profiles()
    print("M26 剖面算术: %d/%d 组 (r, n) 上「暴力枚举 = 参数化 = 期望表」（其中 %d 组非空）; r = 19, n = 3 恰 5 个; "
          "对照: r = 19, n = 3 的 Δ = 1 剖面有 %d 个, 与 Δ = 0 的不相交" % (total, total, nonempty, d1))
    # ---- M27 ----
    rows = []
    for name, (Aa, Bb, Cc, nn) in (("Laderman 23 项", (A, B, C, n)), ("Strassen 7 项", (A2, B2, C2, n2)),
                                  ("标准 n³ 项", schoolbook(3)), ("标准 n³ 项", schoolbook(2))):
        bad, N, cube = check_budget(Aa, Bb, Cc, nn)
        rows.append((name, nn, len(Aa), bad, N, cube))
        assert bad == 0 and N >= cube, rows[-1]
    equal = sum(1 for row in rows if row[4] == row[5])
    for name, nn, r, bad, N, cube in rows:
        print("M27 秩预算(%s, n = %d, r = %d): 分割展平与 P = X·Yᵀ 的失配 %d; N = Σ rank = %d ≥ n³ = %d%s"
              % (name, nn, r, bad, N, cube, "（取等）" if N == cube else ""))
    # 负对照: 预算写成 n³ ≤ N − 1 必须在取等的那些分解上失败
    assert equal >= 2 and all(row[4] >= row[5] for row in rows)
    assert tried > 0 and ok == tried and wrong > 0 and cases > 0 and viol == 0 and mism == 0 and cases2 > 0 and viol2 == 0
    print("TensorRank capacity/profile/budget oracle: ALL_PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
