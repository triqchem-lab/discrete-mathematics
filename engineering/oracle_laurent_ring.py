# ⑦A 数值排假 v2（2026-10-10 加宽版）：函数表示卷积环公理——双类全穷举 + 判别式全穷举
#   C1 = coeffs {-1,0,1} × exps [-1,2]（81 多项式）：结合律 + 分配律（左右）全三元组
#   C2 = coeffs {-2..2} × exps {0,1}（25 多项式）：结合律 + 分配律（左右）全三元组——宽系数类
#   判别式 = mono-conv 全 (c,d,n,m) ∈ {-2..2}²×[-1,2]²（400）+ t·t⁻¹ / t⁻¹·t / t·(−t) 特例
import json, itertools

def conv(f, g):
    out = {}
    for i, a in f.items():
        for j, b in g.items():
            out[i + j] = out.get(i + j, 0) + a * b
    return {k: v for k, v in out.items() if v}

def padd(f, g):
    out = dict(f)
    for k, v in g.items(): out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v}

def mkpolys(coeffs, exps):
    pols = []
    for cs in itertools.product(coeffs, repeat=len(exps)):
        pols.append({e: c for e, c in zip(exps, cs) if c})
    return pols

C1 = mkpolys((-1, 0, 1), range(-1, 3))            # 81
C2 = mkpolys((-2, -1, 0, 1, 2), (0, 1))           # 25
t = {1: 1}; tinv = {-1: 1}; tneg = {1: -1}; R1 = {0: 1}

# ── 判别式特例 ──
assert conv(t, tinv) == R1 and conv(tinv, t) == R1      # t·t⁻¹ = t⁻¹·t = 1
assert conv(t, tneg) == {2: -1}                         # t·(−t) = −t²（tneg-goal-false 判别）
assert conv(tneg, tneg) == {2: 1}                       # (−t)² = t²
assert conv(t, t) == {2: 1} and conv(tinv, tinv) == {-2: 1}

# ── 判别式全穷举：mono-conv（c·tⁿ)(d·tᵐ) = c·d·t^(n+m) ──
n_mono = 0
for c in (-2, -1, 0, 1, 2):
    for d in (-2, -1, 0, 1, 2):
        for n in (-1, 0, 1, 2):
            for m in (-1, 0, 1, 2):
                assert conv({n: c}, {m: d}) == {n + m: c * d} or (c * d == 0 and conv({n: c}, {m: d}) == {})
                n_mono += 1

# ── 全穷举：assoc + distrib（左右）──
a1 = d1 = a2 = d2 = 0
for f in C1:
    for g in C1:
        for h in C1:
            assert conv(f, conv(g, h)) == conv(conv(f, g), h); a1 += 1
            assert conv(f, padd(g, h)) == padd(conv(f, g), conv(f, h)); d1 += 1
            assert conv(padd(g, h), f) == padd(conv(g, f), conv(h, f)); d1 += 1
for f in C2:
    for g in C2:
        for h in C2:
            assert conv(f, conv(g, h)) == conv(conv(f, g), h); a2 += 1
            assert conv(f, padd(g, h)) == padd(conv(f, g), conv(f, h)); d2 += 1
            assert conv(padd(g, h), f) == padd(conv(g, f), conv(h, f)); d2 += 1

total = a1 + d1 + a2 + d2 + n_mono + 5
print(f"C1(81) assoc={a1} distrib={d1} | C2(25,widen) assoc={a2} distrib={d2} | mono={n_mono} + specials=5 | total={total}")
print("ORACLE-MANIFEST", json.dumps({
    "basis": "exact-int", "domain": total, "points": total,
    "claim": "LaurentCubical ring-laws v2 (widen): C1=81(coeffs{-1,0,1}x[-1,2]) full assoc+distrib-both; C2=25(coeffs{-2..2}x{0,1}) full assoc+distrib-both; mono-conv full 400 on {-2..2}^2x[-1,2]^2; specials t*tinv=1 both orders, t*(-t)=-t^2, (-t)^2=t^2"}))
