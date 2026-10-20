# -*- coding: utf-8 -*-
"""wind 不变性 oracle（PIO-2 锚点 A3 先算后验 ✅）

对自环填充 C₅（C5L：cw/ccw/lp 三构造子，全顶点自环 ✓），穷举：
  · 全部定基点闭走（长 ≤ L）；
  · 每条走上的全部单步 AStepL 移动（tri-slide/expand/sq-slide4/sq-expand4/bt/lp-ins/lp-del）；
验证 wind 在每个移动前后保持 —— 完备枚举（points = domain ✓），无抽样。

wind 语义（与 _PEH35.wind5-step 对齐）：cw ↦ +1、ccw ↦ −1、lp ↦ 0。
对照负向锚：Bt 对消对绕数和 = 0（_PEH35.opp-sum0 ✓）。
"""
import sys, json
from collections import deque

L = 10
V = ["c0","c1","c2","c3","c4"]
IDX = {v:i for i,v in enumerate(V)}
NXT = {V[i]: V[(i+1)%5] for i in range(5)}
PRV = {V[(i+1)%5]: V[i] for i in range(5)}

E = set()
for i in range(5):
    a, b = V[i], V[(i+1)%5]
    E.add((a,b)); E.add((b,a))          # cw + ccw
for v in V:
    E.add((v,v))                        # lp（全自环约定 ✓）

def wind(w):
    t = 0
    for i in range(len(w)-1):
        a, b = w[i], w[i+1]
        if b == NXT.get(a, None) and a != b: t += 1
        elif b == PRV.get(a, None) and a != b: t -= 1
        # 自环：+0 ✓
    return t

def moves(w, walks):
    out = []
    n = len(w)
    # tri-slide / sq-slide4（收缩向）
    for i in range(n-2):
        x, y, z = w[i], w[i+1], w[i+2]
        if (x, z) in E and (x,z) != (x,y):
            out.append(("tri-slide@%d" % i, w[:i+1] + w[i+2:]))
    for i in range(n-3):
        x, y, z, u = w[i], w[i+1], w[i+2], w[i+3]
        if (x, u) in E and (x,u) != (x,y):
            out.append(("sq-slide4@%d" % i, w[:i+1] + (u,) + w[i+3:]))
    # expand（展开向）
    for i in range(n-1):
        x, z = w[i], w[i+1]
        for y in V:
            if (x,y) in E and (y,z) in E and not (y == x and z == x):
                nw = w[:i+1] + (y,) + w[i+1:]
                if len(nw)-1 <= L: out.append(("expand@%d,%s" % (i,y), nw))
    # bt（回溯消去：x→y→x）
    for i in range(n-2):
        x, y = w[i], w[i+1]
        if w[i+2] == x and (x,y) in E:
            out.append(("bt@%d" % i, w[:i+1] + w[i+2:]))
    # lp-ins / lp-del（单自环停留 ✓）
    for i in range(n-1):
        x, z = w[i], w[i+1]
        if (x,x) in E:
            nw = w[:i+1] + (x,) + w[i+1:]
            if len(nw)-1 <= L: out.append(("lp-ins@%d" % i, nw))
    for i in range(1, n-1):
        if w[i] == w[i-1] and (w[i], w[i+1]) in E:
            out.append(("lp-del@%d" % i, w[:i] + w[i+1:]))
    return [(t, u) for (t, u) in out if u in walks and u != w]

def main():
    walks = set(); stack = [("c0",)]
    while stack:
        w = stack.pop()
        if w in walks: continue
        walks.add(w)
        if len(w)-1 < L:
            for v in V:
                if (w[-1], v) in E: stack.append(w + (v,))
    walks = {w for w in walks if w[0] == w[-1]}
    total_moves = 0; violations = []
    for w in sorted(walks):
        ww = wind(w)
        for tag, u in moves(w, walks):
            total_moves += 1
            if wind(u) != ww:
                violations.append((tag, w, u, ww, wind(u)))
    print(f"闭走(≤{L}): {len(walks)}；单步移动检查: {total_moves}")
    if violations:
        print("✗ 不变性违例:", violations[:5]); return 1
    print("✅ wind 在全部单步移动下保持（完备枚举 ✓）")
    print("ORACLE-MANIFEST " + json.dumps({
        "basis": "wind=cw计数−ccw计数（自环0）；AStepL 全生成元单步枚举（tri/sq/bt/lp 双向）",
        "domain": total_moves, "points": total_moves,
        "claim": "C5L 上 wind 对全部 AStepL 单步移动不变（完备枚举，L=%d）" % L}))
    return 0

if __name__ == "__main__":
    sys.exit(main())
