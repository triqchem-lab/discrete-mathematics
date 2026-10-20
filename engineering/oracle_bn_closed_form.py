#!/usr/bin/env python3
"""b_n 闭式与块分解恒等式的 oracle 验证（T4，2026-10-20）

断言（全部精确整数，GF(3) 行化简）：
  A. a_n = dim ker F_n           = 3^{n−1} + 2^{n−1}     (n=1..6)
  B. b_n = dim(ker F_n ∩ V_nA)   = 3^{n−1} − 2^{n−1}     (n=1..6)
  C. q_n = dim(ker F_n ∩ im F_n) = 3^{n−1}                (n=1..6)
  D. a_n = 2·a_{n−1} + q_{n−1}                            (n=2..6)
  E. dim(ker F_n² ∩ V_nA) = dim V_nA − b_n                (n=1..5)   ← ④ 互补性
用法：python3 engineering/oracle_bn_closed_form.py
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


def null_basis(A):
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
    return out


def im_basis(A):
    _, piv = rref(A)
    return [A[:, c] for c in piv]


def cap_dim(K, I):
    if not K or not I:
        return 0
    a, b = len(K), len(I)
    comb = np.vstack([np.array(K, dtype=np.int64), np.array(I, dtype=np.int64)])
    _, piv = rref(comb)
    return a + b - len(piv)


rows = []
ok_all = True
for n in range(1, NMAX + 1):
    M, ms, N = F_mat(n)
    K = null_basis(M)
    a_n = len(K)
    q_n = cap_dim(K, im_basis(M))
    Vmask = lambda m: any(x == 0 for x in m)
    b_n = cap_dim(K, [np.eye(N, dtype=np.int64)[i] for i, m in enumerate(ms) if Vmask(m)])
    dimV = 3**n - 2**n
    M2 = (M @ M) % 3
    k2v = (cap_dim(null_basis(M2),
                  [np.eye(N, dtype=np.int64)[i] for i, m in enumerate(ms) if Vmask(m)])
           if n <= 5 else None)
    rows.append(dict(n=n, a=a_n, q=q_n, b=b_n, dimV=dimV, k2v=k2v))

print(f"{'n':>2} {'a_n':>5} {'3^(n-1)+2^(n-1)':>16} {'b_n':>5} {'3^(n-1)-2^(n-1)':>16} "
      f"{'q_n':>5} {'3^(n-1)':>8} {'kerF2∩V':>8} {'V-b_n':>6}")
for r in rows:
    n = r['n']
    ca = 3**(n-1) + 2**(n-1)
    cb = 3**(n-1) - 2**(n-1)
    cq = 3**(n-1)
    ea, eb, eq = r['a'] == ca, r['b'] == cb, r['q'] == cq
    e4 = (r['k2v'] is None) or (r['k2v'] == r['dimV'] - r['b'])
    ok_all &= ea and eb and eq and e4
    print(f"{n:>2} {r['a']:>5} {ca:>16} {r['b']:>5} {cb:>16} {r['q']:>5} {cq:>8} "
          f"{str(r['k2v']):>8} {r['dimV']-r['b']:>6}")

# D: a_n = 2 a_(n-1) + q_(n-1)
for i in range(1, len(rows)):
    pred = 2*rows[i-1]['a'] + rows[i-1]['q']
    if pred != rows[i]['a']:
        ok_all = False
        print(f"  ✗ D 失败 n={rows[i]['n']}: {pred} ≠ {rows[i]['a']}")

print(f"\n全部断言: {'✅ 成立' if ok_all else '❌ 有失败'}")
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基；乘法矩阵 + GF(3) 行化简（精确整数，无浮点）",
    "domain": sum(3**n for n in range(1, NMAX+1)),
    "points": sum(3**n for n in range(1, NMAX+1)),
    "claim": "a_n=3^(n-1)+2^(n-1), b_n=3^(n-1)-2^(n-1), q_n=3^(n-1), "
             "a_n=2a_(n-1)+q_(n-1), dim(kerF^2∩V)=dimV-b_n",
}, ensure_ascii=False))
