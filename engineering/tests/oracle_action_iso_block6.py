#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""块 6 oracle：**作用同构不变性**的完备穷举 + 假设必要性反例。

对应 Agda 节点（proof_dag）：
  B.action.iso-invariant   等变双射连接的两个作用 ⟹ 同一 #orbits
  B.necklace.direction-free  项链作用 ≅ 反向旋转作用 ⟹ 同为 6

完备性（domain == points，非抽样）：
  · 群：阶 ≤ 6 的全部群（复用 oracle_burnside_block3.GROUPS，群论分类穷尽）。
  · 作用：G 生成元到 Sym(p) 的全部满足定义关系者（von Dyck ⇒ 完备）。
  · 同构参数：对每个作用 A 与**每一个**置换 σ ∈ Sym(p)，构造共轭作用
        A^σ :  g ·^σ y = σ (g · σ⁻¹ y)
    并核对三件事：
      ① A^σ 确实是作用（同态律逐个群元对验证）；
      ② σ 在 A 与 A^σ 之间等变（由构造保证，仍显式验证）；
      ③ 轨道大小多重集不变（⇒ #orbits 不变）—— 这正是定理的结论。
  · 假设必要性见证：对每个非平凡作用，检查**是否存在**置换 τ 使
      τ (g · x) ≠ g · (τ x)（即 τ 不是自等变的）—— 这说明「随便一个双射」不够，
      等变性（f-eq / fb-eq）是必要条件，不是形式摆设。
    ⚠ 诚实说明：同一载体上的**共轭**作用 A^σ 天然带等变 σ（由构造保证），
      所以本脚本不构成「不嵌入就不同」的独立见证；它验证的是
      ① 共轭作用仍是作用 ② σ 等变 ③ 轨道结构在共轭下不变（= 定理结论）。

裁决权在 Agda：本脚本只排假命题、给约束；通过 ≠ 证明。
"""

import itertools

from oracle_kit import manifest  # noqa: E402

from oracle_burnside_block3 import GROUPS, hom_ok, orbit_of  # noqa: E402


def orbit_sizes(org, p):
    imgs = [org[s] for s in org]
    seen = set()
    sizes = []
    for x in range(p):
        if x in seen:
            continue
        o = orbit_of(imgs, x)
        seen |= o
        sizes.append(len(o))
    return sorted(sizes)


def conjugate(org, sigma, p):
    """A^σ : g ·^σ y = σ (g · σ⁻¹ y)  —— 使 σ 成为 A → A^σ 的等变双射"""
    inv = [0] * p
    for i in range(p):
        inv[sigma[i]] = i
    return {g: tuple(sigma[org[g][inv[y]]] for y in range(p)) for g in org}


def main():
    domain = 0
    points = 0
    failures = []
    control_witnessed = 0
    total_nontrivial = 0

    for G in GROUPS:
        k = len(G.gens)
        for p in range(1, 6):
            perms = list(itertools.permutations(range(p)))
            cands = [()] if k == 0 else itertools.product(perms, repeat=k)
            for gen_imgs in cands:
                if not hom_ok(G, gen_imgs, p):
                    continue
                org = {s: G.hom_image(s, tuple(gen_imgs), p) for s in G.elems}
                base = orbit_sizes(org, p)
                self_non_equiv = False

                for sigma in itertools.permutations(range(p)):
                    conj = conjugate(org, sigma, p)
                    domain += 1
                    points += 1

                    # ① A^σ 是作用：同态律 (g∘h)·^σ y == g·^σ (h·^σ y)
                    #   （群元素是置换，复合即群乘法 —— 正则表示）
                    # 注意：for g in org 迭代的是**群元素**（不是像）；
                    # 群乘法必须走 G.mul，不能直接拿元素的元组当置换去索引
                    hom_ok_conj = all(
                        conj[G.mul(g, h)]
                        == tuple(conj[g][conj[h][y]] for y in range(p))
                        for g in org for h in org
                    )
                    # ② 等变性 σ (g · x) == g ·^σ (σ x)
                    equiv = all(conj[g][sigma[x]] == sigma[org[g][x]]
                                for g in org for x in range(p))
                    # ③ 轨道大小多重集不变
                    got = orbit_sizes(conj, p)

                    if not hom_ok_conj:
                        failures.append(("NOT-ACTION", G.name, p, gen_imgs, sigma))
                    if not equiv:
                        failures.append(("NOT-EQUIV", G.name, p, gen_imgs, sigma))
                    if got != base:
                        failures.append(("ORBITS-CHANGED", G.name, p, gen_imgs,
                                         sigma, base, got))

                    # 假设必要性见证：该 σ 是否**不是**自等变的
                    if not all(org[g][sigma[x]] == sigma[org[g][x]]
                               for g in org for x in range(p)):
                        self_non_equiv = True

                # 记录「假设必要」的见证存在性（仅供报告，不作失败判据）
                nontrivial = any(org[s] != tuple(range(p)) for s in org)
                if nontrivial:
                    total_nontrivial += 1
                    if self_non_equiv:
                        control_witnessed += 1

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
        claim=("阶≤6 全部群 × Fin p(p≤5) 的全部作用 × Sym(p) 的**每一个**置换 σ："
               "共轭作用 A^σ 仍是作用、σ 等变、轨道大小多重集不变"
               "（⇒ #orbits 不变，即作用同构不变性）；"
               "且报告非平凡作用中「存在非自等变置换」的个数"
               "（等变性是必要条件；p=2 处确实无此见证，属真实情形）"),
    )
    print("全部通过：domain == points == %d（完备穷举，非抽样）" % domain)
    print("非平凡作用：%d 个；其中存在「非自等变置换」见证的：%d 个"
          % (total_nontrivial, control_witnessed))
    print("（缺见证者是真实情形：p=2 时作用像 = Sym(2) 且 Sym(2) 交换 ⟹ 所有置换自等变）")


if __name__ == "__main__":
    main()
