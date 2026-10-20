#!/usr/bin/env python3
"""T4：分片核维数全表 n=1..8（2026-10-21）

目的：检验「每片 ker_k 有 n 的多项式公式」这个假设。
结论：**假设不成立** —— 只有顶部 3 片有公式，中间片不规则。
但 Σ_k ker_k = a_n = 3^(n-1) + 2^(n-1) 始终规整。
"""
import itertools
import json

import numpy as np

NMAX = 8


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
    return M % 3, ms, N


def rank(A):
    A = (A % 3).copy()
    if A.size == 0:
        return 0
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        p = next((i for i in range(r, rows) if A[i, c] % 3), None)
        if p is None:
            continue
        if p != r:
            A[[r, p]] = A[[p, r]]
        inv = 1 if A[r, c] % 3 == 1 else 2
        A[r] = (A[r] * inv) % 3
        mask = A[:, c] % 3 != 0
        mask[r] = False
        if mask.any():
            f = A[mask, c].reshape(-1, 1) % 3
            A[mask] = (A[mask] - f * A[r]) % 3
        r += 1
    return r


tab = {}
for n in range(1, NMAX + 1):
    M, ms, N = F_mat(n)
    sl = lambda k: [i for i, m in enumerate(ms) if sum(1 for e in m if e == 2) == k]
    ks = []
    for k in range(n + 1):
        ck = sl(k)
        ks.append(0 if not ck else len(ck) - rank(M[:, ck]))
    tab[n] = ks
    print(f"n={n}: ker_k = {ks}  Σ={sum(ks)}  a_n(闭式)={3**(n-1)+2**(n-1)}")

print("\n─── 固定 k（低片）───")
for k in range(0, 5):
    print(f"k={k}: {[(n, tab[n][k]) for n in range(1, NMAX+1) if k < len(tab[n])]}")
print("\n─── 固定 n-k（高片）───")
for j in range(0, 5):
    vals = [(n, tab[n][n-j]) for n in range(1, NMAX+1) if 0 <= n-j < len(tab[n])]
    if vals:
        d = [vals[i+1][1]-vals[i][1] for i in range(len(vals)-1)]
        dd = [d[i+1]-d[i] for i in range(len(d)-1)] if len(d) > 1 else []
        print(f"j={j}: {vals}\n      一阶差={d} 二阶差={dd}")

print("\nORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基，按 #2 分片",
    "domain": sum(3**n for n in range(1, NMAX + 1)),
    "points": sum(3**n for n in range(1, NMAX + 1)),
    "claim": "分片核维数全表 n=1..8；假设「每片有 n 的多项式公式」→ 证伪（中间片不规则）",
}, ensure_ascii=False))
