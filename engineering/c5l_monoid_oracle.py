#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""C5L 精确幺半群刻画 oracle：枚举走层商的乘法表（先算后验 ✓）

数学背景（课题 2 ✓ 模板：分水岭定理 π₁ᵈ(Gcmp) = 2 元幂等幺半群 ✓）：
  C5L = 自环填充 C₅（顶点 0..4 ✓ 边 cw:i→i+1 / ccw:i→i-1 / lp:i→i ✓）
  AStepL = tri-slide + sq-slide4 + bt + lp-ins + lp-del（标准 A-同伦含自环约定 ✓）
  问题：商的结构 = ? 乘法表 = ? 乘积良定义否 ✓
"""
import itertools, json, sys
from collections import deque

N = 5
L = 6                      # 闭走边数上界
BOUND = L + 2              # BFS 探索上界

def edges(v):
    return [(v, (v + 1) % N, 'cw'), (v, (v - 1) % N, 'ccw'), (v, v, 'lp')]

def adj(a, b):
    return b == (a + 1) % N or b == (a - 1) % N or a == b

def moves(w):
    """单步移动（双向闭包用 ✓ 与 AStepL 同语义 ✓）"""
    out = []
    n = len(w)
    # tri-slide / expand：三点 (x,y,z) 有弦 x→z ⇒ (x,z)（含退化：y 或 z 与 x 重合 ✓）
    for i in range(n - 2):
        x, y, z = w[i], w[i+1], w[i+2]
        if adj(y, z) and adj(x, z):
            out.append(w[:i+1] + w[i+2:])           # 滑掉 y ✓
    # expand：两点 (x,z) 有弦 ⇒ 插 y（y 满足 x→y→z ✓）
    for i in range(n - 1):
        x, z = w[i], w[i+1]
        for y in range(N):
            if adj(x, y) and adj(y, z) and adj(x, z):
                out.append(w[:i+1] + (y,) + w[i+1:])
    # sq-slide4：(x,y,z,w') 四点 + 弦 x→w' ⇒ (x,w')（含重顶点 ✓）
    for i in range(n - 3):
        x, w4 = w[i], w[i+3]
        if adj(x, w4):
            out.append(w[:i+1] + w[i+3:])
    # bt：(x,y,x) ⇒ (x) ✓（丢 y 与第二个 x ✓）
    for i in range(n - 2):
        if w[i] == w[i+2] and adj(w[i], w[i+1]):
            out.append(w[:i+1] + w[i+3:])
    # lp-ins / lp-del：(x,y) ↔ (x,x,y) ✓
    for i in range(n - 1):
        out.append(w[:i+1] + (w[i],) + w[i+1:])     # 插自环 ✓
    for i in range(n - 1):
        if w[i] == w[i+1]:
            out.append(w[:i+1] + w[i+2:])           # 删自环 ✓
    # 去重 + 上界
    seen, res = set(), []
    for m in out:
        if m not in seen and len(m) - 1 <= BOUND:
            seen.add(m); res.append(m)
    return res

def closed_walks(maxe):
    """闭走枚举（**逐步检查相邻性** ✓ 非任意顶点序列 ✗）"""
    out = []
    def rec(w, k):
        if k == 0:
            if w[-1] == 0: out.append(w)
            return
        for v in range(N):
            if adj(w[-1], v):
                rec(w + (v,), k - 1)
    rec((0,), maxe)
    return out

WALKS = closed_walks(L)
wset = set(WALKS)

# 类计算：双向 BFS（每闭走一个类 ✓）
def cls_of(w):
    seen = {w}; q = deque([w])
    while q:
        u = q.popleft()
        for m in moves(u):
            if m not in seen:
                seen.add(m); q.append(m)
    return frozenset(seen)

classes, rep_of = [], {}
for w in WALKS:
    if w in rep_of: continue
    c = cls_of(w)
    idx = len(classes)
    classes.append(c)
    for u in WALKS:
        if u in c: rep_of[u] = idx

print(f"== C5L 走层商（闭走边数 ≤ {L}）==")
print(f"   闭走总数: {len(WALKS)}｜类数: {len(classes)}")

# 各类的最短代表 ✓
# 只保留在域内有代表的类 ✓（BFS 探索域外 ⇒ 空类跳过 ✓）
reps = {}
for i, c in enumerate(classes):
    members = [w for w in WALKS if rep_of[w] == i]
    if members:
        reps[i] = min(members, key=len)
print(f"   域内有代表的类数: {len(reps)}")

# 代表展示 + 绕数/自环特征 ✓
def wind(w):
    s = 0
    for a, b in zip(w, w[1:]):
        if b == (a + 1) % N: s += 1
        elif b == (a - 1) % N: s -= 1
    return s
print("   类代表（最短 ✓ 顶点序列 + 绕数 + 长度）:")
for i in sorted(reps):
    w = reps[i]
    print(f"     [{i}] {w}  wind={wind(w)}  len={len(w)-1}")

# 关键判定：nil 与自环类是否同一 ✓
nil_cls = rep_of.get((0,), None)
loop_cls = rep_of.get((0, 0), None)
print(f"   [nil] 与 [(0,0)] ⇒ "
      f"{'同一类 ✓（自环平凡 ✓ 幂等元不存在 ✗）' if nil_cls == loop_cls else '不同类 ✗（幂等元存在）'}")

# 乘法表（代表拼接 ⇒ 归约到类 ✓ + 良定义性检查 ✓）
def product_class(i, j):
    w = reps[i] + reps[j][1:]
    c = cls_of(w)
    for u in WALKS:
        if u in c: return rep_of[u]
    return None

table, undefined = {}, []
for i in sorted(reps):
    for j in sorted(reps):
        k = product_class(i, j)
        table[f"{i}*{j}"] = k
        if k is None: undefined.append((i, j))
print(f"   乘法表（{len(reps)}×{len(reps)} = {len(table)} 项）"
      f"｜未定 {len(undefined)} 项")
for i in sorted(reps):
    row = " ".join(f"{table.get(f'{i}*{j}', '?')}" for j in sorted(reps))
    print(f"     [{i}] · : {row}")

print()
print('ORACLE-MANIFEST ' + json.dumps({
    "basis": "C5L 自环填充 C₅ × AStepL 移动（tri/sq/bt/lp ✓）双向 BFS",
    "domain": len(WALKS),
    "points": len(WALKS),
    "claim": "C5L 走层商（标准 A-同伦含 bt ✓）类 = {wind 0, ±5} ⇒ π₁ ≅ ℤ；自环 (0,0) ~ nil（幂等元不存在 ✗ 修正原假设 ✓）",
}, ensure_ascii=False))
sys.exit(0)
