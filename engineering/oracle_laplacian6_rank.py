#!/usr/bin/env python3
"""laplacian6 / laplacian3Replica 在 GF(3)^729 上的秩与核维数（精确整数）。

数学依据（与 Agda 定义逐条对齐）：
  `NSEOnT6SixAxis.agda`
    diffF6 i f x      = f (shiftAt6 i x) ⊕ negate (f x)        -- 前向差分
    axisLap6 i f      = diffF6 i (diffF6 i f)                  -- 单轴二阶差分
    laplacian6 f x    = sum6 (axisLap6 a0 f x) … (axisLap6 a5 f x)
    laplacian3Replica = 轴 a0,a1,a2 各算两次（上游缺陷版）

展开（特征 3，`-2 ≡ 1`）：
    axisLap_i f (x) = f(x+2e_i) − 2·f(x+e_i) + f(x)
                    ≡ f(x+2e_i) + f(x+e_i) + f(x)      (mod 3)
  ⇒ 六轴：对角线 6·f(x) ≡ 0，非对角 12 个邻居各 +1
  ⇒ 三轴复刻：对角线 2·3 ≡ 0，非对角 6 个邻居各 +2

用法：python3 engineering/oracle_laplacian6_rank.py
产物：与模块注释里的 454 / 275、378 / 351 对账（对不上就说明注释数字无据）。
"""
import itertools
import json

import numpy as np

N, D = 3, 6
PTS = list(itertools.product(range(N), repeat=D))
IDX = {p: i for i, p in enumerate(PTS)}
M = len(PTS)


def shift(i, x):
    y = list(x)
    y[i] = (y[i] + 1) % N
    return tuple(y)


def build(axes, mult):
    """Δ 的矩阵：轴列表 axes，每轴贡献乘 mult（复刻版用 2）。"""
    A = np.zeros((M, M), dtype=np.int64)
    for x in PTS:
        r = IDX[x]
        for i in axes:
            y1 = shift(i, x)
            y2 = shift(i, y1)
            A[r, IDX[y1]] += mult       # f(x+e_i)
            A[r, IDX[y2]] += mult       # f(x+2e_i)
            A[r, r] += mult             # f(x)
    return A % 3


def rank_gf3(A):
    """GF(3) 行化简求秩（精确整数，无浮点）。"""
    A = (A % 3).copy()
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if A[i, c] % 3), None)
        if piv is None:
            continue
        if piv != r:
            A[[r, piv]] = A[[piv, r]]
        inv = 1 if A[r, c] % 3 == 1 else 2      # 2*2 ≡ 1 (mod 3)
        A[r] = (A[r] * inv) % 3
        mask = A[:, c] % 3 != 0
        mask[r] = False
        if mask.any():
            f = A[mask, c].reshape(-1, 1) % 3
            A[mask] = (A[mask] - f * A[r]) % 3
        r += 1
        if r == rows:
            break
    return r


SIX = build([0, 1, 2, 3, 4, 5], 1)
THREE = build([0, 1, 2], 2)

r6 = rank_gf3(SIX)
r3 = rank_gf3(THREE)
k6, k3 = M - r6, M - r3

print(f"网格 |T⁶| = {M}")
print(f"laplacian6        : rank = {r6}, kernel = {k6}")
print(f"laplacian3Replica : rank = {r3}, kernel = {k3}")
print()
print("与模块注释（NSEOnT6SixAxis.agda:20）对账：")
print(f"  六轴 注释 454 / 275  → 实算 {r6} / {k6}  "
      f"{'✅ 一致' if (r6, k6) == (454, 275) else '❌ 不一致'}")
print(f"  三轴 注释 378 / 351  → 实算 {r3} / {k3}  "
      f"{'✅ 一致' if (r3, k3) == (378, 351) else '❌ 不一致'}")
print()
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)^6 全网格矩阵（精确整数行化简，无浮点）",
    "domain": M,
    "points": M,
    "claim": f"rank(laplacian6)={r6}, kernel={k6}; rank(laplacian3Replica)={r3}, kernel={k3}",
}, ensure_ascii=False))
