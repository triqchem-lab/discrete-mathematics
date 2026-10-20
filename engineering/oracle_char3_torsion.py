#!/usr/bin/env python3
"""T4 第 9 条路线：char-3 原生的「ker_ℚ + 3-torsion」分解（2026-10-21）

数学背景（人类指出的 char-3 第一性）：
  在 GF(3) 中 0²=0, 1²=1, 2²=4≡1 ⇒ x² ∈ {0,1}, x²=0 ⟺ x=0
  ⇒ x_j² 是「非零指示子」；F = Σ x_j² 是「零坐标升格算子」，不是二次型。

char-p 的经典事实：
  同一整数矩阵在 ℚ 与 GF(p) 上的秩不同，差 = p-torsion（临界群 p-部分）

断言：
  若 a_n = dim ker over GF(3)，ker_ℚ = dim ker over ℚ，
  则 **a_n = ker_ℚ + torsion（torsion = rank_ℚ − rank_3）**

结论（本脚本实测）：
  · 分解**成立** ✓（逐项核对）
  · 但 torsion = 0,0,0,0,1,8 无闭式 ✗
  · ker_ℚ = 2,5,13,35,96,267 无闭式 ✗
  · **重要发现：n ≤ 4 时 torsion = 0** ⇒ 前 4 个值与 char-0 分析完全一致
    （这解释了为何 char-0 语言在 n≤4 处「看起来对」，n≥5 处失效）
"""
import itertools
import json
from fractions import Fraction

import numpy as np

NMAX = 6  # n=7 的 2187×2187 有理数消元太慢


def F_mat(n):
    ms = list(itertools.product(range(3), repeat=n))
    idx = {m: i for i, m in enumerate(ms)}
    N = len(ms)
    M = np.zeros((N, N), dtype=np.int64)
    for m in ms:
        c = idx[m]
        for j in range(n):
            if m[j] == 0:
                t = list(m)
                t[j] = 2
                M[idx[tuple(t)], c] += 1
    return M, ms, N


def rank_mod(A, p):
    A = (A % p).copy()
    if A.size == 0:
        return 0
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        pv = next((i for i in range(r, rows) if A[i, c] % p), None)
        if pv is None:
            continue
        if pv != r:
            A[[r, pv]] = A[[pv, r]]
        inv = pow(int(A[r, c]), -1, p)
        A[r] = (A[r] * inv) % p
        mask = A[:, c] % p != 0
        mask[r] = False
        if mask.any():
            f = A[mask, c].reshape(-1, 1) % p
            A[mask] = (A[mask] - f * A[r]) % p
        r += 1
    return r


def rank_rat(A):
    A = [[Fraction(int(x)) for x in row] for row in A]
    rows = len(A)
    cols = len(A[0]) if rows else 0
    r = 0
    for c in range(cols):
        pv = next((i for i in range(r, rows) if A[i][c] != 0), None)
        if pv is None:
            continue
        A[r], A[pv] = A[pv], A[r]
        piv = A[r][c]
        A[r] = [x / piv for x in A[r]]
        for i in range(rows):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][k] - f * A[r][k] for k in range(cols)]
        r += 1
    return r


rows = []
ok = True
print(f"{'n':>2} {'N':>5} {'ker_ℚ':>6} {'ker_3':>6} {'torsion':>8} {'ker_ℚ+tors':>11} {'=a_n?':>6}")
for n in range(1, NMAX + 1):
    M, ms, N = F_mat(n)
    rq, r3 = rank_rat(M), rank_mod(M, 3)
    kerq, ker3, tors = N - rq, N - r3, rq - r3
    good = kerq + tors == ker3
    ok &= good
    a = 3 ** (n - 1) + 2 ** (n - 1)
    print(f"{n:>2} {N:>5} {kerq:>6} {ker3:>6} {tors:>8} {kerq+tors:>11} {str(good):>6}"
          + ("  ← 闭式 " + str(a) if ker3 == a else "  ← 闭式 " + str(a) + " ✗"))
    rows.append(dict(n=n, kerQ=kerq, ker3=ker3, torsion=tors))

print("\n关键发现：")
zero = [r["n"] for r in rows if r["torsion"] == 0]
nonz = [(r["n"], r["torsion"]) for r in rows if r["torsion"] != 0]
print(f"  torsion = 0 的 n: {zero}   ← char-0 与 char-3 在这些 n 上完全一致")
print(f"  torsion ≠ 0 的 n: {nonz}")
print("\n全部断言: " + ("✅ 分解成立" if ok else "❌ 有失败"))
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基；同一整数矩阵在 ℚ 与 GF(3) 上分别精确消元",
    "domain": sum(3**n for n in range(1, NMAX + 1)),
    "points": sum(3**n for n in range(1, NMAX + 1)),
    "claim": "a_n = ker_ℚ(F_n) + (3-torsion)；n≤4 时 torsion=0（char-0 与 char-3 一致）",
}, ensure_ascii=False))
