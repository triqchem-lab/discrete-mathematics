#!/usr/bin/env python3
"""③b 的结构来源探针：滤链各层维数 + im(F) ∩ ker(x) 的重叠量（T4，2026-10-20）

背景（③a 实算证伪后）：
  `R_n = GF(3)[x₁..x_n]/(x_i³)`，`F = Σ x_j²`，`x = x_n`（末坐标）。
  `a_n = dim ker(F)`，`c_n = dim ker(F²)`。
  坐标分裂 `a_n = a_{n-1} + c_{n-1}` 被证伪 —— 因为 `ker(x) ∩ im(x²) ≠ 0`。

要回答：
  算 1：`dim(im F ∩ ker x)`、`dim(im F² ∩ ker x)` 对 n=1..6，看是否 = `2^{n-2}`
  算 2：`dim ker(x)`、`dim ker(x²)`
  算 3：`c_n` 与上述量的关系

用法：python3 engineering/oracle_filtration_probe.py
"""
import itertools
import json

import numpy as np

NMAX = 6


def monos(n):
    return list(itertools.product(range(3), repeat=n))


def mat_F(n):
    ms = monos(n)
    idx = {m: i for i, m in enumerate(ms)}
    N = len(ms)
    M = np.zeros((N, N), dtype=np.int64)   # 列 = 像
    for m in ms:
        c = idx[m]
        for j in range(n):
            if m[j] == 0:
                t = list(m)
                t[j] = 2
                M[idx[tuple(t)], c] += 1
    return M % 3, ms, idx


def mat_x(n):
    """乘以 x_n（末坐标差分的像）"""
    ms = monos(n)
    idx = {m: i for i, m in enumerate(ms)}
    N = len(ms)
    M = np.zeros((N, N), dtype=np.int64)
    for m in ms:
        c = idx[m]
        if m[n - 1] <= 1:                       # x·x^0 = x, x·x^1 = x², x·x² = x³ = 0
            t = list(m)
            t[n - 1] = m[n - 1] + 1
            M[idx[tuple(t)], c] += 1
    return M % 3


def rref(M):
    M = (M % 3).copy()
    rows, cols = M.shape
    piv, r = [], 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if M[i, c] % 3), None)
        if p is None:
            continue
        if p != r:
            M[[r, p]] = M[[p, r]]
        inv = 1 if M[r, c] % 3 == 1 else 2
        M[r] = (M[r] * inv) % 3
        mask = M[:, c] % 3 != 0
        mask[r] = False
        if mask.any():
            f = M[mask, c].reshape(-1, 1) % 3
            M[mask] = (M[mask] - f * M[r]) % 3
        piv.append(c)
        r += 1
        if r == rows:
            break
    return M, piv


def rank(M):
    return len(rref(M)[1])


def nullspace(M):
    """M 的零空间基（列向量）"""
    R, piv = rref(M)
    cols = M.shape[1]
    free = [c for c in range(cols) if c not in piv]
    basis = []
    for fc in free:
        v = np.zeros(cols, dtype=np.int64)
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-R[i, fc]) % 3
        basis.append(v)
    return basis


def colspace(M):
    R, piv = rref(M)
    return [M[:, c] for c in piv]


print(f"{'n':>2} {'a_n':>6} {'c_n':>6} {'ker x':>6} {'ker x²':>7} "
      f"{'imF∩kerx':>9} {'imF²∩kerx':>10} {'2^(n-2)':>7}")
rows = {}
for n in range(1, NMAX + 1):
    MF, ms, idx = mat_F(n)
    Mx = mat_x(n)
    MF2 = (MF @ MF) % 3

    a_n = len(nullspace(MF))
    c_n = len(nullspace(MF2))
    kx = len(nullspace(Mx))
    kx2 = len(nullspace((Mx @ Mx) % 3))

    def inter(M_im, M_ker):
        """dim(im M_im ∩ ker M_ker)"""
        V = np.array(colspace(M_im))               # 每行是一个生成向量
        K = np.array(nullspace(M_ker))
        # dim(A∩B) = dim A + dim B - dim(A+B)
        A, B = V.shape[0], K.shape[0]
        if A == 0 or B == 0:
            return 0
        AB = np.vstack([V, K])
        return A + B - rank(AB)

    i1 = inter(MF, Mx)
    i2 = inter(MF2, Mx)
    tw = 2 ** (n - 2) if n >= 2 else 0
    rows[n] = dict(a_n=a_n, c_n=c_n, kx=kx, kx2=kx2, imF_cap_kerx=i1,
                   imF2_cap_kerx=i2, two=tw)
    print(f"{n:>2} {a_n:>6} {c_n:>6} {kx:>6} {kx2:>7} {i1:>9} {i2:>10} {tw:>7}")

print()
print("对账：")
print(f"  a_n 公式 3^(n-1)+2^(n-1)：", [3**(n-1)+2**(n-1) for n in range(1, NMAX+1)])
print(f"  c_n 递推 3c_(n-1)-2^(n-2)：", [rows[n]['c_n'] for n in range(1, NMAX+1)])
print()
print("算 1 结论：imF∩kerx 是否 = 2^(n-2)？")
for n in range(2, NMAX + 1):
    ok = "✅" if rows[n]['imF_cap_kerx'] == rows[n]['two'] else "❌"
    print(f"  n={n}: {rows[n]['imF_cap_kerx']} vs {rows[n]['two']} {ok}")
print()
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基；乘法矩阵 + 列空间/零空间/交维数（精确整数行化简）",
    "domain": sum(3**n for n in range(1, NMAX + 1)),
    "points": sum(3**n for n in range(1, NMAX + 1)),
    "claim": "滤链各层维数 + im(F)∩ker(x) 是否 = 2^(n-2)",
}, ensure_ascii=False))
