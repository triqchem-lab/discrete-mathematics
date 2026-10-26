#!/usr/bin/env python3
"""六轴离散 Laplacian 在 GF(3) 上的秩与核维数（精确整数，无浮点）。

被核验的对象 = `NSEOnT6SixAxis.laplacian6` 的**实际定义**：
  axisLap6 i f x = f(x+2eᵢ) + f(x+eᵢ) + f(x)      （GF(3) 上二阶差分 = 整条轴求和）
  laplacian6 f x = Σ_{i=0..5} axisLap6 i f x
⇒ 729×729 矩阵 M[x][y] = #{轴 i : y 与 x 在同一条 i-轴直线上} mod 3。

核验：M 的 GF(3) 秩 = 454，核维数 = 275（729 − 454）。

用法: python3 engineering/verify_nse_rank6.py
"""
import itertools
import json
import sys

import numpy as np

N = 3 ** 6


def idx(x):
    v = 0
    for k in x:
        v = v * 3 + k
    return v


def build():
    M = np.zeros((N, N), dtype=np.int64)
    for x in itertools.product(range(3), repeat=6):
        i = idx(x)
        for a in range(6):
            for k in range(3):
                y = list(x)
                y[a] = (y[a] + k) % 3
                M[i, idx(tuple(y))] += 1
    return M % 3


def rank_gf3(A):
    A = A.copy()
    rank = 0
    for c in range(N):
        piv = next((r for r in range(rank, N) if A[r, c] % 3), None)
        if piv is None:
            continue
        A[[rank, piv]] = A[[piv, rank]]
        if A[rank, c] % 3 == 2:
            A[rank] = (-A[rank]) % 3
        for r in range(N):
            if r != rank and A[r, c] % 3:
                A[r] = (A[r] - A[r, c] * A[rank]) % 3
        rank += 1
    return rank


def main():
    M = build()
    r = rank_gf3(M)
    out = {"n": N, "rank": int(r), "kernel_dim": int(N - r),
           "symmetric": bool((M == M.T).all()),
           "all_row_sums_zero_mod3": bool((M.sum(axis=1) % 3 == 0).all())}
    print(json.dumps(out, indent=1))
    ok = out["rank"] == 454 and out["kernel_dim"] == 275 and out["symmetric"]
    print("ORACLE-MANIFEST " + json.dumps({
        "basis": "729x729 GF(3) matrix: six-axis line-sum Laplacian on (Z/3)^6",
        "domain": N, "points": N,
        "claim": "rank = 454, kernel dimension = 275 over GF(3) (exact integer elimination)"}))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
