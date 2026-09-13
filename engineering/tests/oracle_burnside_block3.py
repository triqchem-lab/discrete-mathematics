#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""块 3 oracle：Burnside 乘法形式 + 通用纤维分解 + 轨道代表元链的**完备**穷举。

对应 Agda 节点（proof_dag）：
  B.sum.fiber        Σ_x f(L x) ≡ Σ_y |fiber_y| · f y
  B.orb.fiber-orbit  标签纤维基数 = 轨道基数
  B.orb.stab-const   同轨道内 |Stab| 相等（块 2）
  B.burnside.main    n · #orbits ≡ Σ_x |Stab x|

完备性论证（domain == points，非抽样）：
  · 群：阶 ≤ 6 的**全部**群。群论分类给出阶 1..6 恰为 C1,C2,C3,C4,V4,C5,C6,S3（8 个），
    本脚本对每个群给出显式乘法表（C_n 为模 n 加法、V4 为 Z2×Z2、S3 为 Sym(3)），无遗漏。
  · 作用：G 的**生成元**到 Sym(p) 的全部映射中满足定义关系者。群同态由生成元上的
    取值唯一决定（von Dyck），故这是 Fin p 上 G-作用的**完备**枚举。
  · 纤维分解：p ≤ 5、m ≤ 4 的全部 (L, f) 组合，无遗漏。
  · 全称精确整数，零浮点。

裁决权在 Agda：本脚本只排假命题、给约束；通过 ≠ 证明，仍须 proof_compile。
"""

import itertools
import sys

from oracle_kit import manifest  # noqa: E402


# ------------------------------------------------------------------ 置换工具
def compose(a, b):
    """(a ∘ b)(x) = a[b[x]]"""
    return tuple(a[b[x]] for x in range(len(a)))


def ident(p):
    return tuple(range(p))


def power(a, k):
    r = ident(len(a))
    for _ in range(k):
        r = compose(a, r)
    return r


def sym(p):
    return list(itertools.permutations(range(p)))


# ------------------------------------------------------- 阶 ≤ 6 的全部群（显式模型）
class Grp:
    """有限群：元素表 + 乘法 + 生成元的定义关系（用于枚举同态）。"""

    def __init__(self, name, elems, mul, e, gens, rels, gen_names):
        self.name = name
        self.elems = elems          # 元素（元组形式，便于作字典键）
        self.mul = mul              # mul(x, y)
        self.e = e
        self.gens = gens            # 生成元元素表
        self.rels = rels            # [(word, target)]：word（生成元下标串）必须等于 target
        self.gen_names = gen_names

    def order(self):
        return len(self.elems)

    def word_of(self, sigma):
        """把元素写成生成元下标串（BFS 树）。"""
        idx = {g: i for i, g in enumerate(self.gens)}
        seen = {self.e: ()}
        frontier = [self.e]
        while frontier:
            nxt = []
            for x in frontier:
                for i, g in enumerate(self.gens):
                    y = self.mul(g, x)
                    if y not in seen:
                        seen[y] = seen[x] + (i,)
                        nxt.append(y)
            frontier = nxt
        return seen[sigma]

    def hom_image(self, sigma, gen_imgs, p):
        """同态 φ 在 sigma 上的像：沿 BFS 字折叠生成元像（作用在 Fin p 上）。"""
        r = ident(p)
        for i in self.word_of(sigma):
            r = compose(gen_imgs[i], r)
        return r


def cycl(n):
    gens = [(1,)] if n >= 2 else []
    rels = [((0,) * n, ())] if n >= 2 else []   # a^n = e（右端是空字 = 恒等置换）
    return Grp("C%d" % n, [(i,) for i in range(n)],
               lambda x, y: (((x[0] + y[0]) % n),),
               (0,), gens, rels, ["a"])


def v4_bits():
    mul = lambda x, y: (x[0] ^ y[0], x[1] ^ y[1])  # noqa: E731
    elems = [(a, b) for a in (0, 1) for b in (0, 1)]
    gens = [(1, 0), (0, 1)]
    rels = [((0, 0), ()), ((1, 1), ()), ((0, 1, 0, 1), ())]   # a²=b²=(ab)²=e
    return Grp("V4", elems, mul, (0, 0), gens, rels, ["a", "b"])


def s3():
    elems = list(itertools.permutations((0, 1, 2)))
    mul = compose
    e = (0, 1, 2)
    a = (1, 2, 0)                              # 3-循环
    b = (1, 0, 2)                              # 对换
    rels = [((0, 0, 0), ()), ((1, 1), ()), ((1, 0, 1, 0), ())]   # a³=b²=(ba)²=e
    return Grp("S3", elems, mul, e, [a, b], rels, ["a", "b"])


GROUPS = [cycl(1), cycl(2), cycl(3), cycl(4), v4_bits(), cycl(5), cycl(6), s3()]


# ---------------------------------------------------------------- 作用与 Burnside
def fold(word, gen_imgs, p):
    r = ident(p)
    for i in word:
        r = compose(gen_imgs[i], r)
    return r


def hom_ok(G, gen_imgs, p):
    """von Dyck：生成元像满足 G 的定义关系 ⟺ 唯一延拓成群同态。

    注意：关系两端都必须是**生成元字**，各自折叠成 Fin p 的置换再比较。
    早期版本把左端折叠结果与硬编码的**群元素**比较 —— 那是类型错误，
    导致群段几乎枚举不出任何作用（实测 120998 里只有 20 条来自群段）。
    """
    for lhs, rhs in G.rels:
        if fold(lhs, gen_imgs, p) != fold(rhs, gen_imgs, p):
            return False
    return True


def orbit_of(images, x):
    """作用在 Fin p 上、生成集给定时 x 的轨道。"""
    seen = {x}
    stack = [x]
    while stack:
        y = stack.pop()
        for g in images:
            z = g[y]
            if z not in seen:
                seen.add(z)
                stack.append(z)
    return seen


def analyse(G, gen_imgs, p):
    """返回 (n, sum_stab, num_orbits, per_x_stab, orb_min_label, ok_flat)。"""
    els = G.elems
    n = len(els)
    imgs = {s: G.hom_image(s, tuple(gen_imgs), p) for s in els}
    sum_stab = 0
    stab = {}
    for x in range(p):
        c = sum(1 for s in els if imgs[s][x] == x)
        stab[x] = c
        sum_stab += c
    # 轨道（取 orbit 的最小元作代表元）
    rep = {}
    for x in range(p):
        rep[x] = min(orbit_of([imgs[s] for s in els], x))
    num_orbits = len(set(rep.values()))
    # 扁平化重排核对：Σ_x |Stab x| == Σ_y |fiber_y| · |Stab y|（y 遍历轨道代表元）
    lhs = sum_stab
    rhs = 0
    for y in set(rep.values()):
        fib = sum(1 for x in range(p) if rep[x] == y)
        rhs += fib * stab[y]
    return n, sum_stab, num_orbits, stab, rep, (lhs == rhs)


def main():
    domain = 0
    points = 0
    failures = []

    # ---- 段 1：Burnside 乘法形式 + 扁平化重排链
    for G in GROUPS:
        k = len(G.gens)
        for p in range(1, 6):
            perms = sym(p)
            if k == 0:
                cands = [()]
            else:
                cands = itertools.product(perms, repeat=k)
            for gen_imgs in cands:
                if not hom_ok(G, gen_imgs, p):
                    continue
                n, sum_stab, orbits, stab, rep, flat_ok = analyse(G, gen_imgs, p)
                domain += 1
                points += 1
                if n * orbits != sum_stab:
                    failures.append(("BURNSIDE", G.name, p, gen_imgs,
                                     n * orbits, sum_stab))
                if not flat_ok:
                    failures.append(("FLATTEN", G.name, p, gen_imgs))
                # 同轨道内 |Stab| 相等（块 2 的算术内容）
                for x in range(p):
                    if stab[x] != stab[rep[x]]:
                        failures.append(("STABEQ", G.name, p, x, stab[x],
                                         stab[rep[x]]))
                # orbit-stabilizer：|Orbit y| · |Stab y| == n
                for y in set(rep.values()):
                    orb = orbit_of([G.hom_image(s, tuple(gen_imgs), p)
                                    for s in G.elems], y)
                    if len(orb) * stab[y] != n:
                        failures.append(("ORBSTAB", G.name, p, y,
                                         len(orb) * stab[y], n))

    # ---- 段 2：通用纤维分解 Σ_x f(L x) == Σ_y |fiber_y| · f y
    for p in range(0, 6):
        for m in range(1, 5):
            for L in itertools.product(range(m), repeat=p):
                for f in itertools.product(range(3), repeat=m):
                    lhs = sum(f[L[x]] for x in range(p))
                    rhs = sum(sum(1 for x in range(p) if L[x] == y) * f[y]
                              for y in range(m))
                    domain += 1
                    points += 1
                    if lhs != rhs:
                        failures.append(("FIBER", p, m, L, f, lhs, rhs))

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
        claim=("阶≤6 全部群 × Fin p(p≤5) 的**全部作用**：n·#orbits == Σ_x|Stab x|，"
               "扁平化重排 Σ_x|Stab x|==Σ_y|fiber_y|·|Stab y|，同轨道 |Stab| 相等，"
               "|Orbit y|·|Stab y|==n；且 p≤5,m≤4 全部 (L,f)：Σ_x f(L x)==Σ_y|fiber_y|·f y"),
    )
    print("全部通过：domain == points == %d（完备穷举，非抽样）" % domain)


if __name__ == "__main__":
    main()
