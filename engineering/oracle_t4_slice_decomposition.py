#!/usr/bin/env python3
"""T4：F 的「#2 分片递升」分解（2026-10-20）

核心结构（本脚本验证）：
  F = Σ_j x_j² 在单项式 x^a 上：F(x^a) = Σ_{j: a_j=0} x^{a+2e_j}
  ⇒ 令 S_k = {a : #2(a) = k}（恰好 k 个坐标指数为 2），则 F: span(S_k) → span(S_{k+1})
  ⇒ 直和分解：
      a_n = Σ_k dim ker(F|_{S_k})                                  （A）
      q_n = Σ_k dim(ker(F|_{S_k}) ∩ im(F|_{S_{k-1}}))               （B）

断言：A 给出 a_n，B 给出 q_n = 3^(n-1)（n=2..5）
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
    if A.size == 0:
        return A, []
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
    if A.size == 0:
        return np.zeros((A.shape[1], 0), dtype=np.int64)
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


def colb(A):
    if A.size == 0:
        return np.zeros((A.shape[0], 0), dtype=np.int64)
    R, piv = rref(A)
    if not piv:
        return np.zeros((A.shape[0], 0), dtype=np.int64)
    return np.array([A[:, c] for c in piv], dtype=np.int64).T


def inter(K, I):
    if K.shape[1] == 0 or I.shape[1] == 0:
        return np.zeros((K.shape[0], 0), dtype=np.int64)
    D = nullb(np.hstack([K, (-I) % 3]) % 3)
    if D.shape[1] == 0:
        return np.zeros((K.shape[0], 0), dtype=np.int64)
    cols = [(K @ D[: K.shape[1], j]) % 3 for j in range(D.shape[1])]
    return colb(np.array(cols, dtype=np.int64).T)


ok = True
for n in range(1, NMAX + 1):
    M, ms, N = F_mat(n)
    S = lambda k: [i for i, m in enumerate(ms) if sum(1 for e in m if e == 2) == k]
    sum_ker, sum_int = 0, 0
    row = []
    for k in range(n + 1):
        ck = S(k)
        if not ck:
            row.append("0")
            continue
        sub = M[:, ck]
        Kk = nullb(sub)
        E = np.zeros((N, len(ck)), dtype=np.int64)
        for i, ci in enumerate(ck):
            E[ci, i] = 1
        KkR = (E @ Kk) % 3
        Ik = colb(M[:, S(k - 1)]) if k > 0 and S(k - 1) else np.zeros((N, 0), dtype=np.int64)
        Jk = inter(KkR, Ik)
        sum_ker += KkR.shape[1]
        sum_int += Jk.shape[1]
        row.append(f"{KkR.shape[1]}/{Jk.shape[1]}")
    a = nullb(M).shape[1]
    q = inter(nullb(M), colb(M)).shape[1]
    e1 = sum_ker == a
    e2 = (n == 1) or (sum_int == q)
    ok &= e1 and e2
    print(f"n={n}: 各片 ker/交 = {' '.join(row)} | Σker={sum_ker}(a={a}){'' if e1 else ' ✗'} | Σ交={sum_int}(q={q}){'' if e2 else ' ✗'}")

print(f"\n全部断言: {'✅ 成立' if ok else '❌ 有失败'}")
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "GF(3)[x]/(x³)^{⊗n} 单项式基，按 #2（指数 2 的个数）分片 S_k",
    "domain": sum(3**n for n in range(1, NMAX + 1)),
    "points": sum(3**n for n in range(1, NMAX + 1)),
    "claim": "a_n = Σ_k dim ker(F|_{S_k})；q_n = Σ_k dim(ker(F|_{S_k}) ∩ im(F|_{S_{k-1}}))",
}, ensure_ascii=False))
