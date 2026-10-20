#!/usr/bin/env python3
"""T4：q_n 与 a_n/b_n/c_n 的结构恒等式验证（2026-10-20）

断言（GF(3) 精确整数，行化简）：
  A. q_n = dim(ker F ∩ im F) = c_n − a_n            (n=1..6)
  B. a_n − b_n = 2^n                                 (n=1..6)
  C. a_{n+1} = a_n + c_n                             (n=1..5)
其中 a_n = dim ker F_n, c_n = dim ker F_n², b_n = dim(ker F_n ∩ V_nA)。

设计：im F ∩ ker F = F(ker F²)，因为 F(q) ∈ ker F ⟺ F²q = 0。
"""
import itertools
import json

import numpy as np

NMAX = 6


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


def rref(A):
    A = (A % 3).copy()
    rows, cols = A.shape
    piv, r = [], 0
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
        piv.append(c)
        r += 1
        if r == rows:
            break
    return A, piv


def nullb(A):
    R, piv = rref(A)
    cols = A.shape[1]
    free = [c for c in range(cols) if c not in piv]
    out = []
    for fc in free:
        v = np.zeros(cols, dtype=np.int64)
        v[fc] = 1
        for i, pc in enumerate(piv):
            v[pc] = (-R[i, fc]) % 3
        out.append(v)
    return np.array(out, dtype=np.int64).T if out else np.zeros((cols, 0), dtype=np.int64)


def colbasis(A):
    R, piv = rref(A)
    if not piv:
        return np.zeros((A.shape[0], 0), dtype=np.int64)
    return np.array([A[:, c] for c in piv], dtype=np.int64).T


def intersect(K, I):
    if K.shape[1] == 0 or I.shape[1] == 0:
        return np.zeros((K.shape[0], 0), dtype=np.int64)
    D = nullb(np.hstack([K, (-I) % 3]) % 3)
    if D.shape[1] == 0:
        return np.zeros((K.shape[0], 0), dtype=np.int64)
    cols = [(K @ D[: K.shape[1], j]) % 3 for j in range(D.shape[1])]
    return colbasis(np.array(cols, dtype=np.int64).T)


rows = []
for n in range(1, NMAX + 1):
    M, ms, N = F_mat(n)
    K = nullb(M)
    a = K.shape[1]
    q = intersect(K, colbasis(M)).shape[1]
    c = nullb((M @ M) % 3).shape[1]
    Vcols = np.array(
        [np.eye(N, dtype=np.int64)[i] for i, m in enumerate(ms) if any(x == 0 for x in m)],
        dtype=np.int64,
    ).T
    b = intersect(K, Vcols).shape[1] if Vcols.shape[1] else 0
    rows.append(dict(n=n, a=a, b=b, c=c, q=q))

print(f"{'n':>2} {'a_n':>4} {'b_n':>4} {'c_n':>4} {'q_n':>4} {'c-a':>4} {'a-b':>4} {'2^n':>4}")
ok = True
for r in rows:
    n = r["n"]
    e1 = r["q"] == r["c"] - r["a"]
    e2 = r["a"] - r["b"] == 2**n
    ok &= e1 and e2
    print(
        f"{n:>2} {r['a']:>4} {r['b']:>4} {r['c']:>4} {r['q']:>4} "
        f"{r['c']-r['a']:>4} {r['a']-r['b']:>4} {2**n:>4}   "
        f"{'✓q' if e1 else '✗q'}{'✓2' if e2 else '✗2'}"
    )
for i in range(len(rows) - 1):
    e3 = rows[i + 1]["a"] == rows[i]["a"] + rows[i]["c"]
    ok &= e3
    if not e3:
        print(f"  ✗ C 失败 n={rows[i]['n']}")

print(f"\n全部断言: {'✅ 成立' if ok else '❌ 有失败'}")
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基；乘法矩阵 + GF(3) 行化简（精确整数，无浮点）",
    "domain": sum(3**n for n in range(1, NMAX + 1)),
    "points": sum(3**n for n in range(1, NMAX + 1)),
    "claim": "q_n = c_n - a_n（im F ∩ ker F = F(ker F²)）；a_n - b_n = 2^n；a_{n+1} = a_n + c_n",
}, ensure_ascii=False))
