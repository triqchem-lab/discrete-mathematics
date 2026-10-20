#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""T1d 桥接 oracle：C₅ 上 bt-free 闭走 ⇒ wind = ±length（先算后验 ✓）

数学断言（_PEH44 的 ℤ 形态）：闭走 w 若 bt-free（无相邻回溯对），
则其 wind（cw +1 / ccw −1 之和）= +len 或 −len ✓。

域：C₅ 上长度 ≤ L 的全部闭走（穷举 ✓ points = domain ✓）。
"""
import itertools, json, sys

L = 8
# C₅：顶点 0..4，cw: i → i+1 mod 5，ccw: i → i-1 mod 5
def step(v, d):  # d = +1 (cw) / -1 (ccw)
    return (v + d) % 5

def all_closed_walks(L):
    """全部长度 0..L 的闭走（顶点序列 ✓ 穷举 ✓）"""
    out = []
    for n in range(0, L + 1):
        for dirs in itertools.product([+1, -1], repeat=n):
            v = 0
            for d in dirs:
                v = step(v, d)
            if v == 0:
                out.append(dirs)
    return out

def is_bt_free(dirs):
    """无相邻回溯对：dirs[i+1] == -dirs[i] 即回溯 ✗"""
    return all(not (dirs[i + 1] == -dirs[i]) for i in range(len(dirs) - 1))

def wind(dirs):
    return sum(dirs)

walks = all_closed_walks(L)
checked = 0
violations = []
bt_free_count = 0
for w in walks:
    if not is_bt_free(w):
        continue
    bt_free_count += 1
    checked += 1
    n = len(w)
    wd = wind(w)
    if not (wd == n or wd == -n):
        violations.append((w, wd, n))
    # 顺带核：bt-free ⇒ 单调（_PEH43 ✓）
    if len(set(w)) > 1:
        violations.append(("NOT-MONOTONE", w))

# 反向对照（判官会说「不」吗 ✓）：有回溯的闭走不应普遍满足 wind = ±len
non_bt = [w for w in walks if not is_bt_free(w)]
non_bt_ok = sum(1 for w in non_bt if wind(w) in (len(w), -len(w)))
print(f"== C₅ 闭走穷举（长度 ≤ {L}）==")
print(f"   闭走总数        : {len(walks)}")
print(f"   bt-free 闭走数  : {bt_free_count}")
print(f"   其中违例（wind ≠ ±len 或非单调）: {len(violations)}")
print(f"   反向对照：非 bt-free 闭走 {len(non_bt)} 条，其中 wind = ±len 者 {non_bt_ok} 条"
      f"（{'判官会说「不」✓' if non_bt_ok < len(non_bt) else '⚠ 判官无效'}）")
if violations:
    print("   违例样例:", violations[:3])
print()
print('ORACLE-MANIFEST ' + json.dumps({
    "basis": "C₅ 双向环（cw/ccw）长度 ≤ 8 全部闭走",
    "domain": len(walks),
    "points": len(walks),
    "claim": "bt-free 闭走 ⇒ wind = ±len 且单调（零违例）",
}, ensure_ascii=False))
sys.exit(0 if not violations else 1)
