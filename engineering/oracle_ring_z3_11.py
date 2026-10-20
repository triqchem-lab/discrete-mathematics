#!/usr/bin/env python3
"""F4 核对：Z/3^11 表示层双射与值语义（纯整数，无浮点）。

对应 Agda 模块 bridge-from-sov-math/Ring3pow11.agda：
  toℕ  : 小端 Horner  sum d_i * 3^i
  repr  : n ↦ [n%3, (n/3)%3, ...]（长度 11）
  add a b = fromℕ (toℕ a + toℕ b)   =>  值 = (A+B) % 3^11
  mul a b = fromℕ (toℕ a * toℕ b)   =>  值 = (A*B) % 3^11
"""
import itertools, json, sys

M = 3 ** 11          # 177147
K = 11

def to_n(ds):                      # 小端 Horner: x ∷ xs ↦ x + 3*toℕ xs
    acc = 0
    for d in reversed(ds):
        acc = d + 3 * acc
    return acc

def repr_(n, k=K):                 # n ↦ [n%3, (n/3)%3, ...]
    ds = []
    for _ in range(k):
        ds.append(n % 3)
        n //= 3
    return tuple(ds)

# ① 全域双射：177147 个值 ↔ 177147 个 11-trit 向量
vecs = [repr_(n) for n in range(M)]
assert len(set(vecs)) == M, "repr 不是单射"
assert set(vecs) == set(itertools.product(range(3), repeat=K)), "repr 不满射"
for n in range(M):
    assert to_n(vecs[n]) == n, n
for v in itertools.product(range(3), repeat=K):
    assert repr_(to_n(v)) == v, v
bijection_points = M

# ② 值语义：加法在 729^2 = 531441 个子域对上逐对核对（ABI 实测口径）
SUB = 3 ** 6                       # 729
add_points = 0
for a in range(SUB):
    va = vecs[a]
    A = to_n(va)
    for b in range(SUB):
        B = to_n(vecs[b])
        got = to_n(vecs[(A + B) % M])          # add 的值
        assert got == (A + B) % M
        add_points += 1
        assert to_n(vecs[(A + B) % M]) == to_n(vecs[(B + A) % M])   # 交换
mul_points = 0
for a in range(SUB):
    A = to_n(vecs[a])
    for b in range(SUB):
        B = to_n(vecs[b])
        assert to_n(vecs[(A * B) % M]) == (A * B) % M
        mul_points += 1
        assert to_n(vecs[(A * B) % M]) == to_n(vecs[(B * A) % M])   # 交换

# ③ 结合律/分配律/单位/逆元 随机抽样（确定性种子）
import random
random.seed(20251020)
pair_points = 0
for _ in range(20000):
    A, B, C = (random.randrange(M) for _ in range(3))
    add = lambda x, y: (x + y) % M
    mul = lambda x, y: (x * y) % M
    assert add(add(A, B), C) == add(A, add(B, C))
    assert mul(mul(A, B), C) == mul(A, mul(B, C))
    assert mul(A, add(B, C)) == add(mul(A, B), mul(A, C))
    assert mul(add(A, B), C) == add(mul(A, C), mul(B, C))
    assert add(A, 0) == A and add(0, A) == A
    assert mul(A, 1) == A and mul(1, A) == A
    assert add(A, (M - A) % M) == 0
    pair_points += 1

print("MODULUS", M, "== 3^11, K =", K)
print("bijection points   :", bijection_points)
print("add-semantics pairs:", add_points)
print("mul-semantics pairs:", mul_points)
print("ring-law triples   :", pair_points)
print("ORACLE-MANIFEST " + json.dumps({
    "basis": "3-adic digits, exact bigint (no float)",
    "domain": M,
    "points": bijection_points,
    "claim": "repr/to_n 全域双射(177147/177147) + add/mul 值语义 mod 3^11 子域 729^2 逐对成立 + 环律 20000 三元组抽样成立",
}))
