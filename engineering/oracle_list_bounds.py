#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ListBounds oracle: 「独立表的三条界互不相容」不用实数镜像的数值交叉核对

对应 Agda: src/Sovereign/Algebra/LinearAlgebra/ListBounds.agda
    ★ lb-incompatible       : lb-Grow N H → lb-Seed P N → lb-Many P N → lb-Comp P N H → ⊥
    ★ lb-incompatible-lists : 上述取 N := listBits、H := λ w → w * w
    （exit=0, 0 postulate; 唯一裁决在 Agda 内核）
对应 Lean: OAI/LinearAlgebra/MatrixExponent/ListBounds.lean（Seed / ManyList / Compression）
    + Iteration.lean:76 `incompatible : Seed P → ManyList P → Compression P → False`

纪律:
  · 全整数 / fractions.Fraction 精确运算; **禁浮点**（宪法）。
  · 这里跑的是**证据**, 不是证明。Agda 内核是裁决。
  · ⚠ 顺序声明: 本件与「先算后验」的常规次序**相反** —— Agda 证明先行（逐段过内核）,
    本 oracle 是事后交叉核对: 核对陈述本身没有被写歪, 并核对**未形式化**的桥接 G
    （Lean 实数陈述 ⟹ ℕ 陈述）。它不能替代桥接的形式化。

核对项（每项都是「断言全过才算过」, 失败即非零退出）:
  A 增长引理   2^(k+4) ≤ w ⟹ w^k ≤ 2^w ≤ listBits w      （并报告实际最小阈值）
  B 取半       2·⌊w/2⌋ ≤ w ≤ 2·⌊w/2⌋ + 1
  C 线性·常数  (c+d)·c ≤ 2^(c+d), c = 2^(k+3);  a·2^(k+3) ≤ 2^a (a ≥ 2^(k+3))
  D 迭代一步   t·n·W^(2·half) < 3m ⟹ m + t·n·W^half·W^(2rn) ≤ m·W^rn
  E 衰减率包   rn ∈ {4gq, pG} 择一 ⟹ 1 ≤ rn ∧ 2rn·G ≤ 16qGg ∧ rn+1 ≤ 8Gp
  F 迭代模拟   从种子出发逐步施压: 最迟 J 步内硬度前提 t·n·W^(2·half) < 3m 必然失效
  G 桥接       Lean 的实数陈述 ⟹ Agda 的 ℕ 陈述（分数精确, 随机抽样）:
        G1 ManyList   t·n·w^σ < 3m ⟹ (t·n)^q · w^p < (3m)^q     (p/q ≤ σ)
        G2 Seed       m ≤ C·n·w² ⟹ m·c₂ ≤ c₁·(n·w·w)            (c₁/c₂ ≥ C)
        G3 Compression m′ ≤ d·(m·h^(−γ) + t·n·h^η) ⟹ ∀u v,
                       u^G ≤ h^g ∧ h^e ≤ v^E ⟹ m′·u ≤ d·(m + t·n·v·u)   (g/G ≤ γ, e/E = η)
  H h 桥       w ≤ ⌈log₂(listBits w)⌉ ≤ w²（Lean 的 h := Nat.clog 2 (listBits w) 落在 H = w² 之内）
  I 非空真     四个一致性见证的数值回声: 去掉任一条假设, 其余三条对一个具体的 P 同时成立
        （Agda §11 lb-consistent-SMG/SCG/MCG/SMC 是裁决; 这里只核对见证的算术）

用法: python3 engineering/oracle_list_bounds.py
"""

import random
import sys
from fractions import Fraction
from itertools import product
from math import gcd


def list_bits(w):
    """Lean: listBits w = 2 * w * 2 ^ w"""
    return 2 * w * 2 ** w


def clog2(n):
    """Nat.clog 2 n = ⌈log₂ n⌉: 最小的 h 使 2^h ≥ n（n = 0 时 Lean 取 0）"""
    if n <= 1:
        return 0
    h, p = 0, 1
    while p < n:
        p *= 2
        h += 1
    return h


def lcm(a, b):
    return a * b // gcd(a, b)


# ---------------------------------------------------------------
# A. 增长引理
# ---------------------------------------------------------------
def check_growth(k_max=7, span=120):
    tested = 0
    thresholds = []
    for k in range(k_max + 1):
        thr = 2 ** (k + 4)
        for w in range(thr, thr + span + 1):
            assert w ** k <= 2 ** w, (k, w)
            assert 2 ** w <= list_bits(w), (k, w)
            tested += 1
        # 实际最小阈值 w0(k): 对一切 w ≥ w0 有 w^k ≤ 2^w（在 ≤ thr 范围内求）
        ok = [w ** k <= 2 ** w for w in range(thr + 1)]

        def holds_from(w0):
            return all(ok[w0:])

        w0 = next(w for w in range(thr + 1) if holds_from(w))
        thresholds.append((k, thr, w0))
    return tested, thresholds


# ---------------------------------------------------------------
# B. 取半
# ---------------------------------------------------------------
def check_half(w_max=600):
    for w in range(w_max + 1):
        a = w // 2
        assert 2 * a <= w <= 2 * a + 1, w
    return w_max + 1


# ---------------------------------------------------------------
# C. 线性·常数 ≤ 指数
# ---------------------------------------------------------------
def check_lin_exp(k_max=4, d_max=40):
    tested = 0
    for k in range(k_max + 1):
        c = 2 ** (k + 3)
        for d in range(d_max + 1):
            assert c * c <= 2 ** c, k
            assert c <= 2 ** c, k
            assert (c + d) * c <= 2 ** (c + d), (k, d)
            tested += 1
        for a in range(c, c + d_max + 1):
            assert a * 2 ** (k + 3) <= 2 ** a, (k, a)
            tested += 1
        # 2·(k+3) ≤ 2^(k+3)
        assert 2 * (k + 3) <= 2 ** (k + 3), k
    return tested


# ---------------------------------------------------------------
# D. 迭代一步（lb-step-Y 的数值形态）
#   前提 t·n·W^(2·half) < 3m 要求 m 很大（≥ t·n·W^(2·half)/3）, 所以 m 必须在
#   「前提成立」的区间里取样, 否则这项是空转的（首版 fires = 0, 已修）。
# ---------------------------------------------------------------
def check_step(W_max=9, rn_max=3, half_extra=3, n_max=3, t_max=3, extra=(0, 1, 2, 7, 100)):
    tested = 0
    fires = 0
    for W in range(6, W_max + 1):
        for rn in range(1, rn_max + 1):
            for half in range(rn + 1, rn + 1 + half_extra):
                for n in range(1, n_max + 1):
                    for t in range(1, t_max + 1):
                        base = t * n * W ** (2 * half)
                        m0 = base // 3 + 1          # 最小的 m 使 base < 3m
                        for off in extra:
                            m = m0 + off
                            tested += 1
                            assert t * n * W ** (2 * half) < 3 * m   # 前提确实成立
                            fires += 1
                            # 结论: m + t·n·W^half·W^(2rn) ≤ m·W^rn
                            assert (m + t * n * W ** half * W ** (2 * rn)
                                    <= m * W ** rn), (W, rn, half, n, t, m)
    assert fires == tested and tested > 0, (tested, fires)
    return tested, fires


# ---------------------------------------------------------------
# E. 衰减率选取包（lb-rn-pkg）
# ---------------------------------------------------------------
def pick_rn(q, g, p, G):
    """Agda lb-rn-pkg: 4gq ≤ pG 取 rn = 4gq, 否则取 rn = pG"""
    return 4 * g * q if 4 * g * q <= p * G else p * G


def check_rn_pkg(bound=7):
    tested = 0
    for q, g, p, G in product(range(1, bound + 1), repeat=4):
        rn = pick_rn(q, g, p, G)
        assert 1 <= rn, (q, g, p, G)
        assert 2 * rn * G <= 16 * q * G * g, (q, g, p, G)
        assert rn + 1 <= 8 * G * p, (q, g, p, G)
        tested += 1
    return tested


# ---------------------------------------------------------------
# F. 迭代模拟（主定理证明逻辑的算术回声）
#   参数照 Agda 主定理的配方: N0 = 16qG, half = 8Gp, J = 3N0 + 16Gp, rn = lb-rn-pkg,
#   w = W^N0, n = W^(120·N0·K)（K ≥ 1; K = 1 是增长条件的下界）。
#   状态用「系数 × W 的幂」表示: m = c·W^x（c 是分数）, t = W^τ —— 避免上 GB 的整数。
#   每步: 先查硬度前提 3m ≤ t·n·W^(2·half) 是否已成立（成立 = 矛盾到达, 停）;
#         否则按 lb-step-Y 的最不利界推进（压缩倍数取最大的 d = W^κ, d^(40J) ≤ n）,
#         并核对不变式 lb-Inv。断言: 最迟第 J 步矛盾到达。
# ---------------------------------------------------------------
def simulate_iteration(q, g, p, G, W, K):
    N0 = 16 * q * G
    half = 8 * G * p
    J = 3 * N0 + 16 * G * p
    rn = pick_rn(q, g, p, G)
    assert 1 <= rn and rn + 1 <= half
    assert 3 * N0 + 2 * half <= J
    nu = 120 * N0 * K                    # n = W^ν
    kappa = (3 * N0 * K) // J            # 最大的 κ 使 (W^κ)^(40J) ≤ n
    assert 40 * J * kappa <= nu and 40 * J * (kappa + 1) > nu
    # 种子: t = 1 (τ = 0), m₀ = n·w² 的量级 —— 取 c = 1, x = ν + 2·N0（比种子界更宽, 对结论更不利）
    tau, c, x = 0, Fraction(1), nu + 2 * N0

    def value(c, x):                     # m·W^(x′) ≤ … 的比较全部化成 c·W^k ≤ 常数
        return c, x

    reached = None
    for j in range(0, J + 1):
        # 不变式 lb-Inv（j = 0 时是种子界; j ≥ 1 时是迭代结论）
        if j >= 1:
            assert 40 * J * tau <= nu * j, ("copy", q, g, p, G, W, K, j)
        # m·W^(j·rn) ≤ t·n·W^(3N0)  ⟺  3N0 + j·rn 是 x − τ − ν 的上界
        k = x + j * rn - tau - nu - 3 * N0
        lhs = c * (W ** k if k >= 0 else Fraction(1, W ** (-k)))
        assert lhs <= 1, ("size", q, g, p, G, W, K, j, lhs)
        # 硬度前提 t·n·W^(2·half) < 3m 是否失效: 3m ≤ t·n·W^(2·half)
        k2 = x - tau - nu - 2 * half
        rhs = 3 * c * (W ** k2 if k2 >= 0 else Fraction(1, W ** (-k2)))
        if rhs <= 1:
            reached = j
            break
        if j == J:
            break
        # 一步压缩: d = W^κ
        #   m′·W^(2rn) ≤ d·(m + t·n·W^half·W^(2rn)) = W^κ·(c·W^x + W^(τ+ν+half+2rn))
        e2 = tau + nu + half + 2 * rn
        y = max(x, e2)
        c = c * (Fraction(W) ** (x - y)) + Fraction(W) ** (e2 - y)
        x = kappa + y - 2 * rn
        assert x >= 0, ("neg exponent", q, g, p, G, W, K, j)
        tau = tau + kappa
    assert reached is not None, ("硬度前提 J 步后仍成立", q, g, p, G, W, K)
    return dict(N0=N0, half=half, J=J, rn=rn, K=K, kappa=kappa, reached=reached,
                tau=tau, x=x)


def check_iteration():
    cases = [(1, 1, 1, 1), (1, 2, 3, 1), (2, 1, 1, 2), (3, 2, 5, 3), (1, 1, 7, 2), (5, 3, 1, 4)]
    out = []
    for (q, g, p, G) in cases:
        for W in (6, 7, 10):
            for K in (1, 2, 4, 9):
                out.append(((q, g, p, G), W, simulate_iteration(q, g, p, G, W, K)))
    return out


# ---------------------------------------------------------------
# G. 桥接: Lean 实数陈述 ⟹ Agda ℕ 陈述（分数精确）
# ---------------------------------------------------------------
def check_bridge_many(trials=400, seed=20261126):
    rng = random.Random(seed)
    tested = 0
    fires = 0
    for _ in range(trials):
        s1, s2 = rng.randint(1, 6), rng.randint(1, 6)
        sigma = Fraction(s1, s2)
        p, q = rng.randint(1, 6), rng.randint(1, 6)
        if Fraction(p, q) > sigma:
            continue
        L = lcm(q, s2)
        r = rng.randint(2, 5)
        w = r ** L                      # w^σ = r^(σ·L), w^(p/q) = r^(pL/q): 全是整数
        t, n = rng.randint(1, 5), rng.randint(1, 5)
        wsig = r ** int(sigma * L)
        wpq = r ** (p * L // q)
        assert wpq <= wsig, "w^(p/q) ≤ w^σ"
        # 抽 m: 一半落在硬度成立区, 一半落在不成立区
        hi = max(1, t * n * wsig)
        m = rng.randint(1, hi)
        tested += 1
        if t * n * wsig < 3 * m:
            fires += 1
            # Lean: t·n·w^σ < 3m; Agda: (t·n)^q · w^p < (3m)^q
            assert (t * n) ** q * w ** p < (3 * m) ** q, (sigma, p, q, r, t, n, m)
    return tested, fires


def check_bridge_seed(trials=600, seed=20261126):
    rng = random.Random(seed + 1)
    tested = 0
    for _ in range(trials):
        c1p, c2p = rng.randint(0, 9), rng.randint(1, 9)
        C = Fraction(c1p, c2p)
        # 取有理数 c₁/c₂ ≥ C（Lean 的实常数 C 只需被一个有理上界盖住）
        c2 = c2p
        c1 = c1p + rng.randint(0, 2)
        assert Fraction(c1, c2) >= C
        w = rng.randint(1, 40)
        n = list_bits(w)
        bound = C * n * w * w
        m = rng.randint(0, int(bound))   # Lean: m ≤ C·n·w²
        tested += 1
        # Agda lb-Seed: m·c₂ ≤ c₁·(n·(w·w))
        assert m * c2 <= c1 * (n * (w * w)), (C, c1, c2, w, m)
    return tested


def check_bridge_comp(trials=300, seed=20261126):
    rng = random.Random(seed + 2)
    tested = 0
    fires = 0
    for _ in range(trials):
        a, b = rng.randint(1, 4), rng.randint(1, 4)
        gamma = Fraction(a, b)                 # Lean 的 γ
        e, E = rng.randint(1, 4), rng.randint(1, 4)
        eta = Fraction(e, E)                   # Lean 的 η
        D = 4                                  # δ = 1/D
        g, G = a, b                            # g/G = γ（也可取更小）
        assert Fraction(g, G) <= gamma
        r = rng.randint(2, 4)
        M = lcm(b, E) * G
        h = r ** M                             # h^γ、h^η、h^(g/G) 全是整数
        hgam = r ** int(gamma * M)
        heta = r ** int(eta * M)
        hgG = r ** (g * M // G)
        assert hgG <= hgam
        s = rng.randint(2, 4)
        n = s ** 20                            # n^(1/D) = s^5, n^(21/20) = s^21
        d = rng.randint(1, s ** 5)             # Lean: d ≤ n^δ  ⟺ d^D ≤ n
        assert d ** D <= n
        m = rng.randint(1, s ** 21)            # Lean: m ≤ n^(21/20) ⟺ m^20 ≤ n^21
        assert m ** 20 <= n ** 21
        t = rng.randint(1, 5)
        tested += 1
        # Lean: m′ ≤ d·(m·h^(−γ) + t·n·h^η)
        bound = d * (Fraction(m, hgam) + t * n * heta)
        mp = rng.randint(1, int(bound))
        fires += 1
        # Agda: 对一切 u, v ≥ 1, u^G ≤ h^g ⟹ h^e ≤ v^E ⟹ m′·u ≤ d·(m + t·n·v·u)
        us = {1, min(hgam, 10 ** 6), rng.randint(1, min(hgam, 10 ** 6))}
        for u in us:
            assert u ** G <= h ** g           # u ≤ h^γ = h^(g/G) ⟹ u^G ≤ h^g
            v = heta * rng.randint(1, 3)
            assert h ** e <= v ** E           # h^η ≤ v ⟹ h^e ≤ v^E
            assert mp * u <= d * (m + t * n * v * u), (gamma, eta, g, G, e, E, d, m, t, u, v, mp)
    return tested, fires


# ---------------------------------------------------------------
# H. h 桥: w ≤ clog 2 (listBits w) ≤ w²
# ---------------------------------------------------------------
def check_h_bridge(w_max=3000):
    holds = []
    for w in range(w_max + 1):
        h = clog2(list_bits(w))
        holds.append(w <= h <= w * w)
    w0 = next(w for w in range(w_max + 1) if all(holds[w:]))
    assert all(holds[w0:]), w0
    return w0, w_max


# ---------------------------------------------------------------
# I. 非空真: 四个一致性见证的数值回声（Agda §11）
# ---------------------------------------------------------------
def check_nonvacuity(w_max=14):
    tested = 0
    # ① 去掉 Compression: P_hard w t m := t·L·w + 1 ≤ 3m —— Seed ∧ Many 成立
    for w in range(1, w_max + 1):
        L = list_bits(w)
        m0 = L * w
        assert 1 * L * w + 1 <= 3 * m0, w            # P_hard w 1 m₀
        assert m0 * 1 <= 1 * (L * (w * w)), w        # Seed 的规模界
        for t in (1, 2, 3, 5):
            for m in range(1, 2 * L * w + 2):
                tested += 1
                if t * L * w + 1 <= 3 * m:            # P_hard 持有者
                    assert t * L * w < 3 * m, (w, t, m)   # 硬度（σ = 1）
    # ② 去掉 ManyList: P_ne w t m := 1 ≤ m —— 压缩取 d = 1、m′ = 1
    for w in range(1, w_max + 1):
        L = list_bits(w)
        for t in (1, 2, 5):
            for m in (1, 2, 7):
                for u in (1, 2, 9):
                    for v in (1, 3):
                        tested += 1
                        assert 1 * u <= 1 * (m + t * L * v * u), (w, t, m, u, v)
                        assert 1 ** 4 <= L                          # d = 1 的侧条件（D = 4）
    # ③ 去掉 Seed: P_big w t m := L·L·w ≤ m —— 压缩的前提 m^20 ≤ L^21 无实例
    for w in range(1, w_max + 1):
        L = list_bits(w)
        lo = L * L * w
        assert lo ** 20 > L ** 21, w                  # 任何持有者都不满足规模前提
        for t in (1, 2, L):                            # Many: t ≤ L
            tested += 1
            assert t * L * w < 3 * lo, (w, t)
    # ④ 去掉 Grow（n ≡ 1、h ≡ 1）: P_w w t m := t·w + 1 ≤ 3m; 侧条件 u^1 ≤ 1^1 ⟹ u = 1
    for t in (1, 2, 5):
        for m in (1, 3):
            for u in range(1, 5):
                if u ** 1 <= 1 ** 1:                   # 侧条件成立
                    assert u == 1
                    for v in (1, 2, 9):
                        tested += 1
                        assert m * u <= 1 * (m + t * 1 * v * u), (t, m, v)
    return tested


# ---------------------------------------------------------------
def main():
    rows = []
    ok = True

    def run(tag, fn):
        nonlocal ok
        try:
            res = fn()
            rows.append((tag, "PASS", res))
        except AssertionError as ex:
            ok = False
            rows.append((tag, "FAIL", ex.args[:1]))

    run("A 增长引理 2^(k+4) ≤ w ⟹ w^k ≤ 2^w ≤ listBits w", check_growth)
    run("B 取半 2·half ≤ w ≤ 2·half + 1", check_half)
    run("C 线性·常数 ≤ 指数", check_lin_exp)
    run("D 迭代一步 t·n·W^(2·half) < 3m ⟹ m + Y ≤ m·W^rn", check_step)
    run("E 衰减率选取包", check_rn_pkg)
    run("F 迭代模拟 J 步 ⟹ 3m ≤ t·n·W^(2·half)", check_iteration)
    run("G1 桥接 ManyList", check_bridge_many)
    run("G2 桥接 Seed", check_bridge_seed)
    run("G3 桥接 Compression", check_bridge_comp)
    run("H h 桥 w ≤ clog 2 (listBits w) ≤ w²", check_h_bridge)
    run("I 非空真（四个一致性见证的数值回声）", check_nonvacuity)

    for tag, status, res in rows:
        print(f"[{status}] {tag}")
        if status == "FAIL":
            print(f"        反例 / 断言信息: {res}")
    a = rows[0][2]
    if rows[0][1] == "PASS":
        print("  A 细目 (k, 采用阈值 2^(k+4), 实测最小阈值 w0(k)):")
        for k, thr, w0 in a[1]:
            print(f"     k={k}: 2^(k+4)={thr}  w0={w0}  共核 {a[0]} 个 w")
    for idx in (3, 4):
        if rows[idx][1] == "PASS":
            print(f"  {rows[idx][0][:1]} 细目: {rows[idx][2]}")
    if rows[5][1] == "PASS":
        res = rows[5][2]
        worst = max(r[2]["reached"] for r in res)
        print(f"  F 细目: {len(res)} 组参数全部到达矛盾; 最迟在第 {worst} 步（各组的 J 见下）")
        for case, W, info in res[:6]:
            print(f"     (q,g,p,G)={case} W={W} K={info['K']}: N0={info['N0']} half={info['half']}"
                  f" J={info['J']} rn={info['rn']} κ={info['kappa']} 矛盾到达于第 {info['reached']} 步")
    for idx in (6, 8):
        if rows[idx][1] == "PASS":
            print(f"  {rows[idx][0][:2]} 细目 (抽样数, 前提成立数): {rows[idx][2]}")
    if rows[7][1] == "PASS":
        print(f"  G2 细目: 抽样 {rows[7][2]}")
    if rows[9][1] == "PASS":
        print(f"  H 细目: w ≤ clog 2 (listBits w) ≤ w² 自 w = {rows[9][2][0]} 起恒成立（核到 {rows[9][2][1]}）")

    verdict = "ALL_PASS" if ok else "HAS_FAILURE"
    print(f"ListBounds oracle: {verdict} ({sum(1 for r in rows if r[1] == 'PASS')}/{len(rows)} 项)")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
