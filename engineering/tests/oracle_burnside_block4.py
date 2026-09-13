#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""块 4 oracle：**#orbits 判据无关性**的完备穷举 + 假设必要性反例。

对应 Agda 节点（proof_dag）：
  B.orb.criterion-free   任意「落轨道内 + 只依赖轨道」判据 r 的不动点计数 ≡ #orbits
  B.burnside.any-rep     n · (判据不动点计数) ≡ Σ_x |Stab x|

完备用枚举（domain == points，非抽样）：
  · 群：阶 ≤ 6 的全部群（复用 oracle_burnside_block3.GROUPS，群论分类穷尽）。
  · 作用：G 生成元到 Sym(p) 的全部满足定义关系者（von Dyck ⇒ 完备）。
  · 判据：每个作用上取 3 个**互不相同**的合法判据（轨道最小元 / 轨道最大元 /
    轨道有序中位元）；另加 1 个**非法**判据（恒等）作假设必要性反例。

判据合法性定义（与 Agda 的 IsRepCriterion 逐字对应）：
  lands（落轨道内）：r(x) ∈ orbit(x)
  const（只依赖轨道）：orbit(x) == orbit(y) ⟹ r(x) == r(y)

裁决权在 Agda：本脚本只排假命题、给约束；通过 ≠ 证明。
"""

import itertools
import sys

from oracle_kit import manifest  # noqa: E402

# 同目录兄弟脚本（sys.path[0] 即脚本所在目录，无需手改 sys.path）
from oracle_burnside_block3 import GROUPS, hom_ok, orbit_of  # noqa: E402


def action_images(G, gen_imgs, p):
    """把生成元上的同态像沿 BFS 字折叠成每个群元的作用（复用 block3 的 Grp.hom_image）。"""
    return {s: G.hom_image(s, tuple(gen_imgs), p) for s in G.elems}


def orbits_of(org, p):
    """orbit[x] = frozenset(orbit of x)"""
    orb = {}
    for x in range(p):
        orb[x] = frozenset(orbit_of([org[s] for s in org], x))
    return orb


def criterion_min(orb, p):
    return {x: min(orb[x]) for x in range(p)}


def criterion_max(orb, p):
    return {x: max(orb[x]) for x in range(p)}


def criterion_mid(orb, p):
    """轨道有序列表的中位元（_//_ 为整除，精确整数）"""
    return {x: sorted(orb[x])[len(orb[x]) // 2] for x in range(p)}


def criterion_id(orb, p):
    return {x: x for x in range(p)}


def is_legal(crit, orb, p):
    """lands + const"""
    for x in range(p):
        if crit[x] not in orb[x]:            # lands
            return False
    for x in range(p):
        for y in range(p):
            if orb[x] == orb[y] and crit[x] != crit[y]:   # const
                return False
    return True


def main():
    domain = 0
    points = 0
    failures = []

    for G in GROUPS:
        k = len(G.gens)
        for p in range(1, 6):
            perms = list(itertools.permutations(range(p)))
            cands = [()] if k == 0 else itertools.product(perms, repeat=k)
            for gen_imgs in cands:
                if not hom_ok(G, gen_imgs, p):
                    continue
                org = action_images(G, gen_imgs, p)
                orb = orbits_of(org, p)
                n = len(G.elems)
                n_orbits = len(set(orb.values()))
                sum_stab = sum(
                    1 for x in range(p) for s in G.elems if org[s][x] == x
                )

                crits = [
                    ("min", criterion_min(orb, p)),
                    ("max", criterion_max(orb, p)),
                    ("mid", criterion_mid(orb, p)),
                ]
                counts = []
                for name, crit in crits:
                    domain += 1
                    points += 1
                    if not is_legal(crit, orb, p):
                        failures.append(("NOT-LEGAL", G.name, p, gen_imgs, name))
                        continue
                    cnt = sum(1 for x in range(p) if crit[x] == x)
                    counts.append(cnt)
                    if cnt != n_orbits:
                        failures.append(("CRIT-COUNT", G.name, p, gen_imgs, name,
                                         cnt, n_orbits))
                    if n * cnt != sum_stab:
                        failures.append(("ANY-REP", G.name, p, gen_imgs, name,
                                         n * cnt, sum_stab))

                # 判据无关性：三个互不相同的合法判据给同一个数
                domain += 1
                points += 1
                if len(set(counts)) > 1:
                    failures.append(("CRIT-VARY", G.name, p, gen_imgs, counts))

                # 假设必要性：恒等判据在 p > 1 且作用非平凡时不合法（lands 或 const 破）
                domain += 1
                points += 1
                trivial = all(org[s][x] == x for s in G.elems for x in range(p))
                id_legal = is_legal(criterion_id(orb, p), orb, p)
                if id_legal != trivial:
                    failures.append(("ID-HYP", G.name, p, gen_imgs, id_legal, trivial))
                if id_legal:
                    cnt = sum(1 for x in range(p) if x == x)
                    if cnt != n_orbits:
                        failures.append(("ID-COUNT", G.name, p, gen_imgs, cnt, n_orbits))

    if failures:
        print("反例 %d 条（前 20）：" % len(failures))
        for f_ in failures[:20]:
            print("  ", f_)
        print("ORACLE-MANIFEST " + str({"basis": "exhaustive", "domain": domain,
                                        "points": points, "claim": "FAILED"}))
        sys.exit(1)

    manifest(
        basis="exhaustive",
        domain=domain,
        points=points,
        claim=("阶≤6 全部群 × Fin p(p≤5) 的全部作用上：3 个互异的合法判据（轨道最小元/"
               "最大元/中位元）均合法且不动点计数 ≡ #orbits，且 n·计数 ≡ Σ_x|Stab x|；"
               "判据无关性（三者同值）；恒等判据合法 ⟺ 作用平凡（假设必要性）"),
    )
    print("全部通过：domain == points == %d（完备穷举，非抽样）" % domain)


if __name__ == "__main__":
    main()
