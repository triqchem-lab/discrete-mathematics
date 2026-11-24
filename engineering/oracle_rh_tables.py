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


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "check"
    {"check": check, "emit": emit, "emit9": emit9, "norm": norm}.get(cmd, check)()
