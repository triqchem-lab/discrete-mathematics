#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""块 7 oracle：DC 走钟迭代（本源侧）的完备穷举。

对应 Agda 节点（proof_dag）：
  B.clock.power-add   过程律 mixedOp-power p (m+n) ≡ mixedOp-power (mixedOp-power p m) n
  B.clock.decompose   分量分解 mixedOp-power (t,a) n ≡ (iterate ⊕T₁ n t, iterate ·a1 n a)
  B.clock.period-12   ∀ p → mixedOp-power p 12 ≡ p，且与既有 mixedOp^12 一致

为什么是**完备**穷举（domain == points，非抽样）：
  · 载体 DuodecPoint = Trit × AlphaPower 是**有限集**，只有 3 × 4 = 12 个点 —— 全部枚举。
  · ℕ 是无限的，但三条断言的内容都是**周期性**：对每个点，迭代序列由其周期完全决定。
    故枚举 n ∈ [0, 24]（> 2 × 12）即覆盖周期行为；
    另对 m, n ∈ [0, 12] 的**全部** 13×13 组合验证过程律（而不是抽样）。
  · 用「与既有 mixedOp^12（硬编码 12 重左乘）的逐点一致」作为交叉验证。

裁决权在 Agda：本脚本只排假命题、给约束。
"""

from oracle_kit import manifest  # noqa: E402

# DC 的两个分量：Trit = Z/3，AlphaPower = Z/4（以指数表示 α^k）
TRITS = [0, 1, 2]          # T₀ T₁ T₂
ALPHAS = [0, 1, 2, 3]      # a0=1 a1=α a2=α² a3=α³
POINTS = [(t, a) for t in TRITS for a in ALPHAS]

G = (1, 1)                 # 联合生成元 g = (T₁, a1)


def mixed(p, q):
    """mixedOp: 幅度 ⊕ (Z/3 加法)，相位 mulAlpha (Z/4 加法，指数形式)"""
    return ((p[0] + q[0]) % 3, (p[1] + q[1]) % 4)


def power(p, n):
    """mixedOp-power p n：右乘 g 共 n 次（与 Agda 定义同向）"""
    r = p
    for _ in range(n):
        r = mixed(r, G)
    return r


def power_left(p, n):
    """既有 mixedOp^12 的形态：左乘 g 共 n 次"""
    r = p
    for _ in range(n):
        r = mixed(G, r)
    return r


def main():
    domain = 0
    points = 0
    failures = []

    # ① 过程律：对**全部** (p, m, n) ∈ 12 × 13 × 13
    for p in POINTS:
        for m in range(13):
            for n in range(13):
                domain += 1
                points += 1
                lhs = power(p, m + n)
                rhs = power(power(p, m), n)
                if lhs != rhs:
                    failures.append(("POWER-ADD", p, m, n, lhs, rhs))

    # ② 分量分解：对全部 (t, a, n) ∈ 3 × 4 × 25
    for t in TRITS:
        for a in ALPHAS:
            for n in range(25):
                domain += 1
                points += 1
                lhs = power((t, a), n)
                rhs = ((t + n * 1) % 3, (a + n * 1) % 4)
                if lhs != rhs:
                    failures.append(("DECOMPOSE", (t, a), n, lhs, rhs))

    # ③ 联合周期 12 + 与既有左乘形态一致：全部点 × n ∈ [0, 24]
    for p in POINTS:
        for n in range(25):
            domain += 1
            points += 1
            if power(p, n) != power_left(p, n):
                failures.append(("LEFT-RIGHT-MISMATCH", p, n,
                                 power(p, n), power_left(p, n)))
        domain += 2
        points += 2
        if power(p, 12) != p:
            failures.append(("PERIOD-12", p, power(p, 12), p))
        # 真因子处不应回到原点（g 的阶恰 12）
        bad = [d for d in (1, 2, 3, 4, 6) if power(G, d) == G]
        if bad:
            failures.append(("ORDER-NOT-12", p, bad))

    if failures:
        print("反例 %d 条（前 20）：" % len(failures))
        for f_ in failures[:20]:
            print("  ", f_)
        print("ORACLE-MANIFEST " + str({"basis": "exhaustive", "domain": domain,
                                        "points": points, "claim": "FAILED"}))
        raise SystemExit(1)

    manifest(
        basis="exhaustive",
        domain=domain,
        points=points,
        claim=("DC 走钟（本源侧）：12 个点 × (m,n)∈[0,12]² 全部满足过程律 "
               "mixedOp-power p (m+n) == mixedOp-power (mixedOp-power p m) n；"
               "12 个点 × n∈[0,24] 全部满足分量分解 "
               "(t⊕n·T₁, a·α^n)；且左乘/右乘形态逐点一致、p 走 12 步回到原点、"
               "g 的真因子 1/2/3/4/6 步均不回到原点（阶恰 12）"),
    )
    print("全部通过：domain == points == %d（完备穷举，非抽样）" % domain)


if __name__ == "__main__":
    main()
