#!/usr/bin/env python3
"""dim ann(Σ x_j²) in GF(3)[x₁..xₙ]/(xᵢ³) —— 结构性公式验证（T4 / 路线 A）

背景（查 1 的结论）：
  `lineSum i f x = f x ⊕ f(x+e) ⊕ f(x+2e)`，char 3 下 `1+s+s² = (s−1)²`
  ⇒ `Δ = Σ_j (s_j−1)²`，即群代数 GF(3)[(C₃)ⁿ] 中**乘以 F = Σ x_j²**（x_j = s_j−1）。
  ⇒ `ker Δ = ann(F)` —— 若它有闭式，则 T4 精确秩**不需要** 729×729 消元。

要回答的两问：
  ① `dim ann(F)` 是否 = 2ⁿ（=「所有 aᵢ ≥ 1」的单项式数）？
  ② 若不等，是否有闭式？（对 n 小值算出来找规律）

用法：python3 engineering/oracle_ann_quadratic.py
"""
import itertools
import json

import numpy as np


def ann_dim(n):
    """在 R = GF(3)[x]/(x³)^{⊗n} 的单项式基上，算乘以 F=Σx_j² 的零空间维数。"""
    monos = list(itertools.product(range(3), repeat=n))
    idx = {m: i for i, m in enumerate(monos)}
    N = len(monos)
    A = np.zeros((N, N), dtype=np.int64)
    for m in monos:
        r = idx[m]
        for j in range(n):
            if m[j] == 0:                      # x_j² 乘上去不溢出（x³→0）
                t = list(m)
                t[j] = 2
                A[r, idx[tuple(t)]] += 1
    A %= 3
    # GF(3) 行化简求秩
    A = A.copy()
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i, c] % 3), None)
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = 1 if A[r, c] % 3 == 1 else 2
        A[r] = (A[r] * inv) % 3
        mask = A[:, c] % 3 != 0
        mask[r] = False
        if mask.any():
            f = A[mask, c].reshape(-1, 1) % 3
            A[mask] = (A[mask] - f * A[r]) % 3
        r += 1
        if r == rows:
            break
    return N - r


print(f"{'n':>2} {'3^n':>6} {'dim ann(F)':>10} {'2^n':>5} {'差':>6}")
vals = {}
for n in range(1, 7):
    d = ann_dim(n)
    vals[n] = d
    print(f"{n:>2} {3**n:>6} {d:>10} {2**n:>5} {d-2**n:>6}")

print()
print("对账：")
print(f"  n=6 时 dim ann(F) = {vals[6]}；oracle 消元给出的 laplacian6 核 = 275")
print(f"  {'✅ 结构公式与消元一致' if vals[6]==275 else '❌ 不一致 —— 结构识别有误'}")
print(f"  n=1..6 = {[vals[n] for n in range(1,7)]}")
print()
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基，乘以 F=Σx_j² 的矩阵（精确整数行化简）",
    "domain": sum(3**n for n in range(1, 7)),
    "points": sum(3**n for n in range(1, 7)),
    "claim": f"dim ann(Σx_j²) for n=1..6 = {[vals[n] for n in range(1,7)]}；n=6 是否 = 275",
}, ensure_ascii=False))
