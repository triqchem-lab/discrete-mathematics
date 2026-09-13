#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""块 5 oracle：**项链计数**（Burnside 的招牌应用）的完备穷举。

对应 Agda 节点（proof_dag）：
  B.burnside.app-necklace   C₄ 在 4-bit 串（= 2 色 4 珠）上的旋转作用 ⟹ 6 条项链
  B.necklace.decomposition  6 条轨道的显式大小分解 1+1+4+4+2+4 = 16

完备性（domain == points，非抽样）：
  · 对珠子数 n = 1..10、颜色数 c = 2..4 的**全部** c^n 着色，逐个算轨道（旋转群 C_n），
    再核对「轨道数 == 显式枚举数」且「Σ_x |Stab x| == n · 轨道数」（Burnside 的定义式）。
  · 另对 n = 4, c = 2 的 16 个着色，逐条打印轨道分解并与 Agda 側硬编码的 6 条轨道对齐。
  · 再对 n = 1..8 核对闭式 Σ_{d|n} φ(d) · c^(n/d) / n 与枚举值相等。

裁决权在 Agda：本脚本只排假命题、给约束。
"""

from oracle_kit import manifest  # noqa: E402


def gcd(a, b):
    """整数 gcd（Euclid；不用 math —— 该模块只返回浮点，被 oracle 禁）"""
    while b:
        a, b = b, a % b
    return a


def phi(n):
    """Euler φ（精确整数）"""
    return sum(1 for k in range(1, n + 1) if gcd(k, n) == 1)


def orbits(n_bits, colours):
    """返回 (轨道列表, 每个着色的稳定子大小)。着色编码为 0..c^n-1 的 base-c 数。"""
    total = colours ** n_bits

    def rotate_code(x):
        digits = []
        t = x
        for _ in range(n_bits):
            digits.append(t % colours)
            t //= colours
        # digits[i] = 位置 i 的颜色；旋转：位置 i 的颜色移到位置 i+1
        vals = [0] * n_bits
        for i in range(n_bits):
            vals[(i + 1) % n_bits] = digits[i]
        r = 0
        for i in range(n_bits - 1, -1, -1):
            r = r * colours + vals[i]
        return r

    group = []
    cur = tuple(range(total))
    seen = set()
    stack = [cur]
    while stack:
        p = stack.pop()
        if p in seen:
            continue
        seen.add(p)
        group.append(p)
        stack.append(tuple(rotate_code(p[x]) for x in range(total)))

    seen_pts = set()
    orb_list = []
    for x in range(total):
        if x in seen_pts:
            continue
        o = set()
        for p in group:
            o.add(p[x])
        seen_pts |= o
        orb_list.append(sorted(o))
    stab = {x: sum(1 for p in group if p[x] == x) for x in range(total)}
    return orb_list, stab


def main():
    domain = 0
    points = 0
    failures = []
    necklaces_4_2 = None
    sizes_4_2 = None

    for n_bits in range(1, 11):
        for colours in range(2, 5):
            orb_list, stab = orbits(n_bits, colours)
            total = colours ** n_bits
            # 计数单位 = **单个着色**（不是 (n,c) 三元组）：这才是真实枚举量
            domain += total
            points += total
            # ① 轨道确实划分全部着色
            if sum(len(o) for o in orb_list) != total:
                failures.append(("PARTITION", n_bits, colours,
                                 sum(len(o) for o in orb_list), total))
            if len(set().union(*orb_list)) != total:
                failures.append(("DUP", n_bits, colours))
            # ② Burnside 定义式：Σ_x |Stab x| == n · #orbits
            s = sum(stab.values())
            if s != n_bits * len(orb_list):
                failures.append(("BURNSIDE", n_bits, colours, s,
                                 n_bits * len(orb_list)))
            # ③ 闭式：Σ_{d|n} φ(d)·c^(n/d) / n
            closed = sum(
                phi(d) * colours ** (n_bits // d)
                for d in range(1, n_bits + 1) if n_bits % d == 0
            ) // n_bits
            if closed != len(orb_list):
                failures.append(("CLOSED-FORM", n_bits, colours, closed,
                                 len(orb_list)))
            if n_bits == 4 and colours == 2:
                necklaces_4_2 = len(orb_list)
                sizes_4_2 = sorted(len(o) for o in orb_list)
                print("n=4, c=2 的轨道分解：")
                for o in sorted(orb_list, key=lambda o: min(o)):
                    print("   {%s}  大小 %d" % (", ".join(str(v) for v in o),
                                                len(o)))

    # 4 珠 2 色的具体断言（与 Agda §4 硬编码的 6 条轨道对齐）
    for want, got in [("6 条项链", necklaces_4_2 == 6),
                      ("轨道大小 {1,1,2,4,4,4}", sizes_4_2 == [1, 1, 2, 4, 4, 4]),
                      ("大小和 = 16", sum(sizes_4_2) == 16)]:
        domain += 1
        points += 1
        if not got:
            failures.append(("4-2-ASSERT", want, necklaces_4_2, sizes_4_2))

    if failures:
        print("反例 %d 条：" % len(failures))
        for f_ in failures[:20]:
            print("  ", f_)
        print("ORACLE-MANIFEST " + str({"basis": "exhaustive", "domain": domain,
                                        "points": points, "claim": "FAILED"}))
        raise SystemExit(1)

    manifest(
        basis="exhaustive",
        domain=domain,
        points=points,
        claim=("珠子数 n=1..10 × 颜色数 c=2..4 的全部 c^n 着色：轨道划分完整、"
               "Burnside 定义式 Σ_x|Stab x| == n·#orbits、闭式 Σ_{d|n}φ(d)c^(n/d)/n "
               "三者一致；且 4 珠 2 色恰 6 条项链、轨道大小 {1,1,2,4,4,4}"),
    )
    print("全部通过：domain == points == %d（完备穷举，非抽样）" % domain)
    print("4 珠 2 色项链数 = %d，轨道大小 = %s" % (necklaces_4_2, sizes_4_2))


if __name__ == "__main__":
    main()
