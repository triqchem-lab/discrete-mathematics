#!/usr/bin/env python3
"""RH 线数值子句生成器与对账器（先算后验 · 全枚举 · 非抽样）

用法:
  python3 -I engineering/oracle_rh_tables.py check    # 对账: 生成值 vs 已写 .agda 的数值声明
  python3 -I engineering/oracle_rh_tables.py emit     # 输出各模块的 Agda 数值子句块（供机械粘贴/比对）
  python3 -I engineering/oracle_rh_tables.py norm     # A2.1: t²+3s²=4·3ⁿ 解分类全枚举（陈述冻结）

全枚举范围:
  · F₃ 判别式 27 组; F₃ 点数/迹 27 组（含奇异）;
  · F₉ 点数/迹 18 组非奇异（F₉ = F₃[x]/(x²+1) 全 9 元枚举）;
  · 范数方程 t²+3s² = 4·3ⁿ 的整数解集（n ≤ 12, |t| ≤ 2·3^{n/2}+2 全域）。
零依赖（纯标准库）。本脚本是 RH 链数值内容的**唯一**权威来源;
.agda 里的数值子句必须与之逐字一致（Agda 内核对已写内容做最终裁决）。
"""
import sys

F3 = [0, 1, 2]
TRIT = ["T₀", "T₁", "T₂"]


# ---------- F₃ ----------
def disc3(a2, a4, a6):
    return (a2 * a2 * a4 * a4 - a4**3 - a2**3 * a6) % 3


def nsol3(v):
    return 1 if v == 0 else (2 if v == 1 else 0)


def pts3(a2, a4, a6):
    return 1 + sum(nsol3((x**3 + a2 * x * x + a4 * x + a6) % 3) for x in F3)


TRI = {0: "T₀", 1: "T₁", 2: "T₂"}


# ---------- F₉ = F₃[x]/(x²+1)：元素 = (a, b)，乘法 (ac+2bd, ad+bc) ----------
def f9mul(u, v):
    a, b = u
    c, d = v
    return ((a * c + 2 * b * d) % 3, (a * d + b * c) % 3)


def f9add(u, v):
    return ((u[0] + v[0]) % 3, (u[1] + v[1]) % 3)


F9 = [(a, b) for a in F3 for b in F3]
ZERO9, ONE9 = (0, 0), (1, 0)


def f9eq(u, v):
    return u == v


def pts9(a2, a4, a6):
    A2, A4, A6 = (a2, 0), (a4, 0), (a6, 0)
    total = 1
    for x in F9:
        x2 = f9mul(x, x)
        x3 = f9mul(x2, x)
        rhs = f9add(f9add(f9add(x3, f9mul(A2, x2)), f9mul(A4, x)), A6)
        total += sum(1 for y in F9 if f9eq(f9mul(y, y), rhs))
    return total


def tr3_of(n):
    return 4 - n


def tr9_of(n):
    return 10 - n  # t₂ = q+1−#E(F₉), q=9


TRI9 = {0: "+ 0", 1: "+ 1", 2: "+ 2", 3: "+ 3"}
NEG9 = {-1: "-[1+ 0 ]", -2: "-[1+ 1 ]", -3: "-[1+ 2 ]", -5: "-[1+ 4 ]", -6: "-[1+ 5 ]"}


def zlit(t):
    return TRI9[t] if t >= 0 else NEG9[t]


# ---------- 范数方程 t²+3s²=4·3ⁿ ----------
def norm_solutions(n):
    q = 3**n
    bound = 2 * 3 ** ((n + 1) // 2) + 2
    out = []
    for t in range(-bound, bound + 1):
        r = 4 * q - t * t
        if r >= 0 and r % 3 == 0:
            s2 = r // 3
            s = int(round(s2**0.5))
            if s * s == s2:
                out.append((t, s))
    return sorted(set(out))


def v3(x):
    v = 0
    while x % 3 == 0 and x:
        x //= 3
        v += 1
    return v


# ---------- 各表 ----------
def table_f3():
    rows = []
    for a2 in F3:
        for a4 in F3:
            for a6 in F3:
                d = disc3(a2, a4, a6)
                n = pts3(a2, a4, a6)
                rows.append((a2, a4, a6, d, n, tr3_of(n), d != 0))
    return rows


def table_f9():
    rows = []
    for a2, a4, a6, d, n3, t3, ok in table_f3():
        if ok:
            n9 = pts9(a2, a4, a6)
            rows.append((a2, a4, a6, n9, tr9_of(n9)))
    return rows


CURVE = lambda a2, a4, a6: f"c{a2}{a4}{a6}"


# ---------- emit ----------
def emit():
    print("=== §CurveF3: 27 条 disc 子句 ===")
    for a2, a4, a6, d, n, t, ok in table_f3():
        print(f"disc-{CURVE(a2,a4,a6)} : discF3 {CURVE(a2,a4,a6)} ≡ {TRI[d]}")
        print(f"disc-{CURVE(a2,a4,a6)} = refl")

    print("\n=== §CountF3: 18 条 pe 子句（非奇异）===")
    for a2, a4, a6, d, n, t, ok in table_f3():
        if ok:
            print(f"pe-{CURVE(a2,a4,a6)} : pointsE {CURVE(a2,a4,a6)} ≡ {n}")
            print(f"pe-{CURVE(a2,a4,a6)} = refl")

    print("\n=== §CountF3: 18 条 tr 子句（ℤ 迹）===")
    for a2, a4, a6, d, n, t, ok in table_f3():
        if ok:
            print(f"tr-{CURVE(a2,a4,a6)} : tℤ {CURVE(a2,a4,a6)} ≡ {zlit(t)}")
            print(f"tr-{CURVE(a2,a4,a6)} = refl")

    print("\n=== §SupersingularF3: 27 条 sup-trace 子句 ===")
    VOF = {1: "trP3", 2: "trP2", 3: "trP1", 4: "trZ", 5: "trM1", 6: "trM2", 7: "trM3"}
    SUP = {"trM3", "trZ", "trP3"}
    for a2, a4, a6, d, n, t, ok in table_f3():
        v = VOF[n]
        sup = v in SUP
        if sup and n == 4:
            body = "inj₂ (inj₁ refl)"
        elif sup:
            body = {7: "inj₁ refl", 1: "inj₂ (inj₂ refl)"}[n]
        else:
            body = "⊥-elim s"
        tag = "⊤" if sup else "⊥"
        print(f"sup-trace (mkC {TRI[a2]} {TRI[a4]} {TRI[a6]}) s = {body}  -- #{n}, t={t:+d}, trV={v} {tag}")

    emit9()
    return


def emit9():
    t3map = {}
    for a2, a4, a6, d, n, t, ok in table_f3():
        if ok:
            t3map[CURVE(a2, a4, a6)] = t
    print("=== §CountF9All: F₉ 枚举序（f9at, 与 oracle F9 = [(a,b) for a in F3 for b in F3] 同序）===")
    print("-- 0:(T₀,T₀) 1:(T₀,T₁) 2:(T₀,T₂) 3:(T₁,T₀) 4:(T₁,T₁) 5:(T₁,T₂) 6:(T₂,T₀) 7:(T₂,T₁) 8:(T₂,T₂)")
    print("\n=== §CountF9All: 18 条 pe9 子句（非奇异）===")
    for a2, a4, a6, n9, t9 in table_f9():
        print(f"pe9-{CURVE(a2,a4,a6)} : pointsE9 {CURVE(a2,a4,a6)} ≡ {n9}")
        print(f"pe9-{CURVE(a2,a4,a6)} = refl")
    print("\n=== §WeilRecurrenceAll: 18 条 (t₁,t₂) 验收对照 ===")
    for a2, a4, a6, n9, t9 in table_f9():
        c = CURVE(a2, a4, a6)
        print(f"-- {c}: t1={t3map[c]:+d}, t2={t9:+d}  (校验 t2 = t1²-6: {(t3map[c]**2 - 6) == t9})")


# ---------- check: 对账已写 .agda ----------
def parse_claims(path, pat):
    import re
    out = {}
    txt = open(path, encoding="utf-8").read()
    for m in re.finditer(pat, txt):
        out[m.group(1)] = m.group(2)
    return out


def check():
    bad = 0
    # CurveF3 disc
    got = parse_claims("src/Sovereign/Application/Problems/RH/CurveF3.agda",
                       r"discF3 (c\d\d\d) ≡ (T[₀₁₂])")
    T = lambda v: TRI[v]
    for a2, a4, a6, d, n, t, ok in table_f3():
        want = T(d)
        have = got.get(CURVE(a2, a4, a6))
        if have != want:
            print(f"  ✗ disc {CURVE(a2,a4,a6)}: .agda={have} oracle={want}"); bad += 1
    print(f"CurveF3 disc 对账: {'一致' if bad == 0 else str(bad) + ' 处不一致'} (27)")

    # CountF3 pe
    got = parse_claims("src/Sovereign/Application/Problems/RH/CountF3.agda",
                       r"pointsE (c\d\d\d) ≡ (\d+)")
    for a2, a4, a6, d, n, t, ok in table_f3():
        if ok:
            have = got.get(CURVE(a2, a4, a6))
            if have != str(n):
                print(f"  ✗ pe {CURVE(a2,a4,a6)}: .agda={have} oracle={n}"); bad += 1
    print(f"CountF3 pe 对账: 一致 (18)" if bad == 0 else f"  累计不一致 {bad}")

    # SupersingularF3 分支体
    txt = open("src/Sovereign/Application/Problems/RH/SupersingularF3.agda", encoding="utf-8").read()
    VOF = {1: "trP3", 2: "trP2", 3: "trP1", 4: "trZ", 5: "trM1", 6: "trM2", 7: "trM3"}
    SUP = {"trM3", "trZ", "trP3"}
    import re
    bad2 = 0
    for m in re.finditer(r"sup-trace \(mkC (T[₀₁₂]) (T[₀₁₂]) (T[₀₁₂])\) s = (.+?)(?:  --|$)", txt, re.M):
        a2, a4, a6 = [{"T₀": 0, "T₁": 1, "T₂": 2}[x] for x in m.groups()[:3]]
        body = m.group(4).strip()
        n = pts3(a2, a4, a6)
        v = VOF[n]
        want = ("inj₂ (inj₁ refl)" if (v in SUP and n == 4)
                else {7: "inj₁ refl", 1: "inj₂ (inj₂ refl)"}[n] if v in SUP
                else "⊥-elim s")
        if body != want:
            print(f"  ✗ sup-trace c{a2}{a4}{a6}: .agda={body!r} oracle={want!r}"); bad2 += 1
    print(f"SupersingularF3 sup-trace 对账: {'一致' if bad2 == 0 else str(bad2) + ' 处不一致'} (27)")

    # CountF9All pe9（存在才对账; 18 条）
    import os
    f9path = "src/Sovereign/Application/Problems/RH/CountF9All.agda"
    bad3 = 0
    if os.path.exists(f9path):
        got = parse_claims(f9path, r"pointsE9 (c\d\d\d) ≡ (\d+)")
        for a2, a4, a6, n9, t9 in table_f9():
            have = got.get(CURVE(a2, a4, a6))
            if have != str(n9):
                print(f"  ✗ pe9 {CURVE(a2,a4,a6)}: .agda={have} oracle={n9}"); bad3 += 1
        print(f"CountF9All pe9 对账: {'一致' if bad3 == 0 else str(bad3) + ' 处不一致'} (18)")

    total = bad + bad2 + bad3
    print(f"\n对账总结: {'全部一致 ✓' if total == 0 else f'{total} 处不一致 ✗'}")
    return total


# ---------- norm (A2.1) ----------
def norm():
    print("=== A2.1: t² + 3s² = 4·3ⁿ 解分类（n ≤ 12 全域枚举）===")
    ok = True
    for n in range(1, 13):
        sols = norm_solutions(n)
        # 冻结判据（v2, 2026-11-24 由枚举否证 v1 整除式后冻结的**有限值形式**）:
        #   n 奇 = 2k+1: t ∈ {0, ±3^(k+1)};  n 偶 = 2k: t ∈ {±3^k, ±2·3^k}
        closed = []
        if n % 2 == 1:
            k = (n - 1) // 2
            cand = [0, 3 ** (k + 1), -(3 ** (k + 1))]
        else:
            k = n // 2
            cand = [3 ** k, -3 ** k, 2 * 3 ** k, -2 * 3 ** k]
        closed = cand
        have = sorted(set(t for t, s in sols))
        if sorted(closed) != have:
            print(f"  ✗ n={n}: 冻结判据 {closed[:8]}… 与枚举 {have[:8]}… 不符"); ok = False
        print(f"  n={n:2d}: 可解 t = {have}  （s 值: {[s for t, s in sols if t in have][:6]}…）")
    # t=0 谱系
    print("\n  t=0 谱系: n 奇 ⇒ 可解 (s=±2·3^{(n−1)/2}); n 偶 ⇒ 无解 (NoNormT0Even 已证)")
    print(f"\n冻结判据核验: {'全部一致 ✓' if ok else '存在不符 ✗'}")
    print("冻结陈述 v2（供 NormClassify.agda；v1 整除式已被 n=7 反例 t=±162 否证）:")
    print("  n = 2k+1 (奇): t ∈ {0, ±3^(k+1)}（恰三值）;  (t,s) = (0,±2·3^k) 或 (±3^(k+1), ±3^k)")
    print("  n = 2k   (偶): t ∈ {±3^k, ±2·3^k}（恰四值）;  (t,s) = (±3^k, ±3^k) 或 (±2·3^k, 0)")
    print("  即: 解集 = 3·解集(n−2)（n≥3 递降），基 n=1: {(0,±2),(±3,±1)}; n=2: {(±3,±3),(±6,0)}")


# ---------- iso (A5.2 续作①): F₃ 同构分类 = x-平移轨道 ----------
def xshift(a2, a4, a6, r):
    # y² = (x+r)³ + a2(x+r)² + a4(x+r) + a6 于 char 3 展开
    # (x+r)³ = x³ + r³;  (x+r)² = x² + 2rx + r²  (3r·x² ≡ 0)
    a4n = (2 * a2 * r + a4) % 3
    a6n = (r**3 + a2 * r * r + a4 * r + a6) % 3
    return (a2, a4n, a6n)


def iso():
    print("=== A5.2①: F₃ 同构分类（x-平移轨道; u-缩放 mod 3 平凡: u⁴≡u⁶≡1）===")
    ns = [(a2, a4, a6) for a2, a4, a6, d, n, t, ok in table_f3() if ok]
    # 不变性交叉核对: disc 与 #E 在平移下不动
    bad = 0
    for c in ns:
        for r in F3:
            c2 = xshift(*c, r)
            if disc3(*c2) != disc3(*c) or pts3(*c2) != pts3(*c):
                print(f"  ✗ 平移不变性破坏: {c} --r={r}--> {c2}"); bad += 1
    print(f"  平移不变性（disc/#E）: {'27×3 全部保持 ✓' if bad == 0 else str(bad) + ' 处破坏 ✗'}")
    # 轨道（限制在 18 条非奇异内; 不动点: 2·a2·r ≡ 0 且 r³+a2r²+a4r ≡ 0 的 r）
    seen = set()
    orbits = []
    for c in ns:
        if c in seen:
            continue
        orb = sorted({xshift(*c, r) for r in F3} & set(ns))
        orbits.append(orb)
        seen |= set(orb)
    orbits.sort(key=lambda o: (-len(o), o[0]))
    print(f"  18 条非奇异 → {len(orbits)} 个平移轨道:")
    tr3map = {}
    for a2, a4, a6, d, n, t, ok in table_f3():
        if ok:
            tr3map[(a2, a4, a6)] = t
    for i, orb in enumerate(orbits):
        ts = {tr3map[c] for c in orb}
        names = " ".join(CURVE(*c) for c in orb)
        flag = "✓" if len(ts) == 1 else "✗ 迹不一致!"
        print(f"  class{i}: [{names}]  t={sorted(ts)} {flag}")
    print()
    print("=== §CurveIsoF3: xshift 逐组公式 ===")
    print("xshift (mkC a2 a4 a6) r = mkC a2 (((T2 * a2) * r) + a4)")
    print("       ((((r * r) * r) + (a2 * (r * r))) + ((a4 * r) + a6)))")

    # ---- 机械子句块（emit-iso: 供 CurveIsoF3.agda 逐字粘贴/比对）----
    TRI3 = {0: "T₀", 1: "T₁", 2: "T₂"}
    cls_of = {}
    for i, orb in enumerate(orbits):
        for c in orb:
            cls_of[c] = i
    rep = {i: orb[0] for i, orb in enumerate(orbits)}

    print("\n=== §CurveIsoF3: disc-shift 81 条（disc 平移不变）===")
    for c in table_f3_names():
        for r in F3:
            print(f"ds-{CURVE(*c)}-{r} : discF3 (xshift {CURVE(*c)} {TRI3[r]}) ≡ discF3 {CURVE(*c)}")
            print(f"ds-{CURVE(*c)}-{r} = refl")

    print("\n=== §CurveIsoF3: pts-shift 81 条（#E 平移不变）===")
    for c in table_f3_names():
        for r in F3:
            print(f"ps-{CURVE(*c)}-{r} : pointsE (xshift {CURVE(*c)} {TRI3[r]}) ≡ pointsE {CURVE(*c)}")
            print(f"ps-{CURVE(*c)}-{r} = refl")

    print("\n=== §CurveIsoF3: cls-of 27 条（9 奇异 absurd + 18 分派; mkC 模式形态）===")
    allc = [(a2, a4, a6) for a2 in F3 for a4 in F3 for a6 in F3]
    for c in allc:
        pat = f"(mkC {TRI3[c[0]]} {TRI3[c[1]]} {TRI3[c[2]]})"
        if c not in cls_of:
            print(f"cls-of {pat} h = ⊥-elim (h refl)")
        else:
            print(f"cls-of {pat} h = cls{cls_of[c]}")

    print("\n=== §CurveIsoF3: ns-ds 54 条（平移目标的非奇异见证 = 目标曲线的 ns-*）===")
    for c in ns:
        for r in F3:
            tgt = xshift(*c, r)
            print(f"ns-ds-{CURVE(*c)}-{r} : IsNonSing {CURVE(*tgt)}")
            print(f"ns-ds-{CURVE(*c)}-{r} = ns-{CURVE(*tgt)}")

    print("\n=== §CurveIsoF3: sic 54 条（独立引理形态 —— nightly 坑#5: 分派子句块前")
    print("    悬置其他已声明未定义签名会污染 refl 检查, 故全件用独立具名引理）===")
    for c in ns:
        for r in F3:
            tgt = xshift(*c, r)
            print(f"sic-{CURVE(*c)}-{r} : cls-of {CURVE(*tgt)} ns-ds-{CURVE(*c)}-{r} ≡ cls-of {CURVE(*c)} ns-{CURVE(*c)}")
            print(f"sic-{CURVE(*c)}-{r} = refl  -- {CURVE(*c)} --r={r}--> {CURVE(*tgt)}")

    print("\n=== §CurveIsoF3: cls-trace 18 条（独立引理形态）===")
    for c in ns:
        i = cls_of[c]
        print(f"ct-{CURVE(*c)} : tℤ {CURVE(*c)} ≡ tℤ (rep-of cls{ i })")
        print(f"ct-{CURVE(*c)} = refl")

    print("\n=== §CurveIsoF3: 轨道成员等式（每轨道内部 xshift 关系, 供 shift-in-cls 反射核）===")
    for i, orb in enumerate(orbits):
        members = " ".join(CURVE(*c) for c in orb)
        print(f"-- cls{i}: {members}")
        for c in orb:
            for r in F3:
                tgt = xshift(*c, r)
                if tgt in set(orb) and tgt != c:
                    print(f"--   {CURVE(*c)} --{TRI3[r]}--> {CURVE(*tgt)}")

    print("\n=== §CurveIsoF3: cls 互斥 28 条（8 取 2; 构造子相异 → ≡ 空）===")
    for i in range(len(orbits)):
        for j in range(i + 1, len(orbits)):
            print(f"ne-cls{i}-{j} : cls{i} ≡ cls{j} → ⊥")
            print(f"ne-cls{i}-{j} ()")

    print(f"\n=== 类代表: {{{', '.join('cls%d: %s' % (i, CURVE(*rep[i])) for i in range(len(orbits)))}}} ===")
    return orbits


def table_f3_names():
    return [(a2, a4, a6) for a2 in F3 for a4 in F3 for a6 in F3]


# ---------- frob (M6·B0): Frobenius sigma 于 E(F9) 的作用 ----------
def f9conj(u):
    # sigma(a + b*alpha) = a + b*alpha^3 = a - b*alpha (alpha^3 = alpha*alpha^2 = -alpha)
    return (u[0], (-u[1]) % 3)


def frob():
    print("=== M6·B0: Frobenius sigma 于 E(F9)（(x,y) ↦ (x̄,ȳ)）===")
    ns = [(a2, a4, a6) for a2, a4, a6, d, n, t, ok in table_f3() if ok]
    n9 = {c: pts9(*c) for c in ns}
    rows = []
    bad = 0
    for c in ns:
        pts = []
        for x in F9:
            x2 = f9mul(x, x)
            x3 = f9mul(x2, x)
            rhs = f9add(f9add(f9add(x3, f9mul((c[0], 0), x2)), f9mul((c[1], 0), x)), (c[2], 0))
            for y in F9:
                if f9mul(y, y) == rhs:
                    pts.append((x, y))
        # sigma 封闭 + sigma^2 = id + Fix 计数（仿射点; 无穷远点单独计, σ-不动）
        sset = set(pts)
        fix = [P for P in pts if f9conj(P[0]) == P[0] and f9conj(P[1]) == P[1]]
        for P in pts:
            sP = (f9conj(P[0]), f9conj(P[1]))
            if sP not in sset:
                print(f"  ✗ {CURVE(*c)}: sigma 不封闭 at {P}"); bad += 1
            s2P = (f9conj(sP[0]), f9conj(sP[1]))
            if s2P != P:
                print(f"  ✗ {CURVE(*c)}: sigma^2 ≠ id at {P}"); bad += 1
        # 总点数 = 1(∞, σ-不动) + 仿射; Fix 总 = 1 + Fix仿射
        total = 1 + len(pts)
        fix_total = 1 + len(fix)
        if total != n9[c]:
            print(f"  ✗ {CURVE(*c)}: 总点数 {total} ≠ pe9 {n9[c]}"); bad += 1
        pairs = (len(pts) - len(fix)) // 2
        rows.append((c, total, fix_total, pairs))
    print(f"  sigma 封闭/σ²=id/总点数=pe9: {'全部一致 ✓' if bad == 0 else str(bad) + ' 处破坏'}")
    print(f"  {'曲线':<6} {'#E9':>4} {'Fix':>4} {'2-cycles':>9}   #E9 = Fix + 2·pairs")
    for c, e9, f, pr in rows:
        print(f"  {CURVE(*c):<6} {e9:>4} {f:>4} {pr:>9}   {e9} = {f} + 2·{pr} {'✓' if e9 == f + 2*pr else '✗'}")
    # Fix 与 #E(F3) 的关系: Fix = E(F3) 嵌入 ⟺ Fix 计数 = #E(F3)
    t3map = {(a2, a4, a6): n for a2, a4, a6, d, n, t, ok in table_f3() if ok}
    print("\n  Fix(σ) 与 #E(F₃)（嵌入判据: 坐标虚部 ≡ T₀）:")
    ok2 = True
    for c, e9, f, pr in rows:
        e3 = t3map[c]
        if f != e3:
            print(f"  ✗ {CURVE(*c)}: Fix {f} ≠ #E(F3) {e3}"); ok2 = False
    print(f"  Fix(σ) = #E(F₃): {'18/18 一致 ✓' if ok2 else '存在不一致 ✗'}")

    print("\n=== §FrobFix: pairs 常量 + split/fe 子句（emit-frob 逐字）===")
    for c, e9, f, pr in rows:
        print(f"pairs-{CURVE(*c)} : ℕ")
        print(f"pairs-{CURVE(*c)} = {pr}")
    print()
    for c, e9, f, pr in rows:
        print(f"split-{CURVE(*c)} : pointsE9 {CURVE(*c)} ≡ fixcnt {CURVE(*c)} + 2 * pairs-{CURVE(*c)}")
        print(f"split-{CURVE(*c)} = refl")
    print()
    for c, e9, f, pr in rows:
        print(f"fe-{CURVE(*c)} : fixcnt {CURVE(*c)} ≡ pointsE {CURVE(*c)}")
        print(f"fe-{CURVE(*c)} = refl")
    return rows


# ---------- group (M6·B5/G0): E(F9) 群律（char 3 一般 Weierstrass）----------
F9ZERO = (0, 0)
F9ONE = (1, 0)


def f9inv(u):
    for v in F9:
        if f9mul(u, v) == F9ONE:
            return v
    raise ValueError(f"no inverse for {u}")


F9INV_TAB = {u: f9inv(u) for u in F9 if u != F9ZERO}


def e9pts(c):
    # E(F9) 全点: None = 无穷远点 + 仿射点
    a2, a4, a6 = c
    pts = [None]
    for x in F9:
        x2 = f9mul(x, x)
        x3 = f9mul(x2, x)
        rhs = f9add(f9add(f9add(x3, f9mul((a2, 0), x2)), f9mul((a4, 0), x)), (a6, 0))
        for y in F9:
            if f9mul(y, y) == rhs:
                pts.append((x, y))
    return pts


def f9neg(u):
    return ((-u[0]) % 3, (-u[1]) % 3)  # 全分量求负（共轭只负 α 分量, 二者不同 —— 实测坑）


def e9neg(c, P):
    if P is None:
        return None
    return (P[0], f9neg(P[1]))  # -(x,y) = (x,-y); x 不变


def e9add(c, P, Q):
    if P is None:
        return Q
    if Q is None:
        return P
    xP, yP = P
    xQ, yQ = Q
    a2, a4, a6 = c
    if xP == xQ and f9add(yP, yQ) == F9ZERO:
        return None  # P = -Q: yP + yQ = 0（含 y=0 的 2-挠; 减法判据是 P=Q 的, 实测坑）
    if P == Q:
        num = f9add(f9mul((2, 0), f9mul((a2, 0), xP)), (a4, 0))  # char 3: 3x^2 = 0
        den = f9add(yP, yP)
        lam = f9mul(num, F9INV_TAB[den])
    else:
        lam = f9mul(f9add(yQ, f9neg(yP)), F9INV_TAB[f9add(xQ, f9neg(xP))])
    x3 = f9add(f9add(f9mul(lam, lam), f9neg((a2, 0))), f9add(f9neg(xP), f9neg(xQ)))
    y3 = f9add(f9mul(lam, f9add(xP, f9neg(x3))), f9neg(yP))
    return (x3, y3)


def e9mulint(c, n, P):
    # [n]P 逐次加法（n 可负; 0 -> 无穷远）
    R = None
    for _ in range(abs(n)):
        R = e9add(c, R, P if n > 0 else e9neg(c, P))
    return R


def group():
    print("=== M6·B5/G0: E(F9) 群律（char 3 一般形; oracle 全枚举核对）===")
    ns = [(a2, a4, a6) for a2, a4, a6, d, n, t, ok in table_f3() if ok]
    t3map = {(a2, a4, a6): t for a2, a4, a6, d, n, t, ok in table_f3() if ok}
    bad = 0
    for c in ns:
        pts = e9pts(c)
        t = t3map[c]
        sset = set(pts)
        # 单位/逆/封闭
        for P in pts:
            if e9add(c, P, None) != P or e9add(c, None, P) != P:
                print(f"  ✗ {CURVE(*c)}: 单位元失败"); bad += 1
            N = e9neg(c, P)
            if N not in sset or e9add(c, P, N) is not None:
                print(f"  ✗ {CURVE(*c)}: 逆元失败 at {P}"); bad += 1
        # 交换律 + 结合律（全点）
        for P in pts:
            for Q in pts:
                if e9add(c, P, Q) != e9add(c, Q, P):
                    print(f"  ✗ {CURVE(*c)}: 交换律失败 {P},{Q}"); bad += 1
        for P in pts:
            for Q in pts:
                for R in pts:
                    if e9add(c, e9add(c, P, Q), R) != e9add(c, P, e9add(c, Q, R)):
                        print(f"  ✗ {CURVE(*c)}: 结合律失败 {P},{Q},{R}"); bad += 1
        # sigma 群自同: sigma(P+Q) = sigma P + sigma Q（全对）
        for P in pts:
            for Q in pts:
                S = e9add(c, P, Q)
                lhs = None if S is None else (f9conj(S[0]), f9conj(S[1]))
                sP = None if P is None else (f9conj(P[0]), f9conj(P[1]))
                sQ = None if Q is None else (f9conj(Q[0]), f9conj(Q[1]))
                rhs = e9add(c, sP, sQ)
                if lhs != rhs:
                    print(f"  ✗ {CURVE(*c)}: sigma 群自同失败 {P},{Q}"); bad += 1
        # 特征方程点级: [4]P = [t].sigma P（全点; sigma 不动点与 2-cycles 都覆盖）
        for P in pts:
            SP = None if P is None else (f9conj(P[0]), f9conj(P[1]))
            lhs = e9mulint(c, 4, P)
            rhs = e9mulint(c, t, SP)
            if lhs != rhs:
                print(f"  ✗ {CURVE(*c)}: 特征方程失败 [4]{P} != [{t}]sigma({P})"); bad += 1
        if bad > 40:
            break
    print(f"  群公理(单位/逆/交换/结合全点) + sigma 群自同 + 特征方程 [4]P=[t].sigma P:"
          f" {'18 曲线全部通过 ✓' if bad == 0 else str(bad) + ' 处失败 ✗'}")
    # 各类点数速览（供 G1 量级评估: 代表元曲线的点数 x 点数 = 加法表格数）
    reps = [(0, 1, 0), (1, 0, 1), (1, 0, 2), (2, 0, 1), (2, 0, 2), (0, 2, 0), (0, 2, 1), (0, 2, 2)]
    total = 0
    print("\n  8 类代表元点数（G1 表格量级 = n^2）:")
    for c in reps:
        n = len(e9pts(c))
        total += n * n
        print(f"  {CURVE(*c)}: {n} 点 -> 加法表 {n}^2 = {n*n} 格")
    print(f"  8 类合计加法表格数: {total}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    {"check": check, "emit": emit, "emit9": emit9, "norm": norm, "iso": iso, "emit-iso": iso, "frob": frob, "emit-frob": frob, "group": group}.get(cmd, check)()
