#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""M16 oracle: GF(3) 上 2×2 矩阵乘法张量的 7 项秩分解（Strassen）的结构常数恒等式

先算后验纪律（memory: py-enumerate-before-agda-clauses）:
  · 张量 T(x,y,z) = [x.1 = z.1][x.2 = y.1][y.2 = z.2]（x = (i,j) 左输入位置, y = (j,k) 右输入, z = (i,k) 输出）
  · Strassen 的七门拆成 α_k·β_k（A 的线性型 × B 的线性型）与输出系数 c_k(z)
  · 判据一: Σ_k α_k(x)·β_k(y)·c_k(z) ≡ T(x,y.z) 对全部 4·4·4 = 64 个指标三元组成立
  · 判据二（独立路径）: 对全部 3⁸ = 6561 组矩阵输入,
                      Σ_k (α_k·A)(β_k·B)·c_k(z) ≡ (A·B)(z) —— 走普通矩阵乘法, 不经判据一
  · 判据三（两路会合）: 16 对基矩阵 × 4 个输出 = 64 次比对, 判据一 / 判据二 / 普通矩阵乘法逐值一致
  · 三条路径必须同时成立才算数。
    另可按指标三元组发射 64 条 refl 子句（emit_clauses）; Agda 件 `TensorRankGF3.agda` **没有**贴用它们,
    实际组织是「任意矩阵的接桥 + 16 对基矩阵 × 4 个输出位置的 refl（mm-basis）」, 数值对应就是判据三。
M16-B（展平下界 n² ≤ r 的计数证法）的数值检验:
  · 取 Strassen 的真实分解（上面的 α, β, c）, 固定 k, 按证明里的构造
        w x₀ i = β_i(y₀)·c_i(z₀),   t_λ i = Σ_{x₀} λ(x₀)·w x₀ i,   (Φ t) x = Σ_i t i·α_i(x)
    对随机 λ 逐点核对 Φ(t_λ) ≡ λ —— 即「标准基落在张成里 ⟹ 一切函数都在张成里」的构造。
  · 随机生成元 a（r < n²）时, 张成里装不下全部标准基（n = 2, r = 3 随机抽样无一成功）;
    r ≥ n² 时存在装得下的 a（标准基本身）。
M16-C（秩相乘 / 取幂, 镜像 Lean RankPower.lean）的数值检验:
  · 两个秩分解的张量积仍是秩分解: 取 Strassen ⊗ Strassen, 得 ⟨4,4,4⟩ 的 49 项分解
    (指标编码 combine i j = i·m + j)。判据四: 全部 16³ = 4096 个结构常数三元组;
    判据五(独立路径): 随机 4×4 矩阵上走普通 4×4 矩阵乘法。
  · ⟨1⟩ 的 1 项分解(rank-one), 以及有限证书 7^6 ≤ 2^17(即 (7^k)^6 ≤ (2^k)^17 对一切 k)。
M16-D（「ω = 9/4」两半的有限语言, 镜像 Lean FieldExtension.lean:72 exponent_lt_iff_rank）的数值检验:
  · Strassen 覆盖: q ≥ 1 且 17q ≤ 6p ⟹ (7^(6q))^q < (2^(6q))^p（Agda: strassen-saving）
  · 两半不重叠: n ≥ 2、n^9 ≤ r^4（下半）且 r^q < n^p（节省）⟹ 9q < 4p（Agda: saving-above）
    负对照: 去掉「n^9 ≤ r^4」后该蕴含不成立（n=2, r=1, q=1, p=1）。
禁浮点; 全部是 GF(3) 上的整数运算。
"""
import sys
from itertools import product

F3 = (0, 1, 2)
POS = [(0, 0), (0, 1), (1, 0), (1, 1)]   # (行, 列)


def add(x, y):
    return (x + y) % 3


def mul(x, y):
    return (x * y) % 3


def neg(x):
    return (-x) % 3


def dot(u, a):
    """线性型 u（位置 → 系数, 顺序同 POS）在矩阵 a（位置 → 值）上的取值"""
    return sum(mul(c, a[p]) for c, p in zip(u, POS)) % 3


# 线性型: 位置 → 系数（长度 4, 顺序同 POS）
# A 的七个线性型 α（Strassen 1969）
ALPHA = [
    [1, 0, 0, 1],    # a + d
    [0, 0, 1, 1],    # c + d
    [1, 0, 0, 0],    # a
    [0, 0, 0, 1],    # d
    [1, 1, 0, 0],    # a + b
    [2, 0, 1, 0],    # c − a
    [0, 1, 0, 2],    # b − d
]
# B 的七个线性型 β
BETA = [
    [1, 0, 0, 1],    # e + h
    [1, 0, 0, 0],    # e
    [0, 1, 0, 2],    # f − h
    [2, 0, 1, 0],    # g − e
    [0, 0, 0, 1],    # h
    [1, 1, 0, 0],    # e + f
    [0, 0, 1, 1],    # g + h
]
# 输出系数 c_k(z), z ∈ POS; 行 = 门 k, 列 = 输出位置
#   out00 = m1 + m4 − m5 + m7;  out01 = m3 + m5;  out10 = m2 + m4;  out11 = m1 − m2 + m3 + m6
C = [
    [1, 0, 0, 1],    # m1: out00, out11
    [0, 0, 1, 2],    # m2: out10, −out11
    [0, 1, 0, 1],    # m3: out01, out11
    [1, 0, 1, 0],    # m4: out00, out10
    [2, 1, 0, 0],    # m5: −out00, out01
    [0, 0, 0, 1],    # m6: out11
    [1, 0, 0, 0],    # m7: out00
]


def tensor(x, y, z):
    """T(x,y,z): 三个指标条件的合取（0/1）"""
    return 1 if (x[0] == z[0] and x[1] == y[0] and y[1] == z[1]) else 0


def struct_const(x, y, z):
    """Σ_k α_k(x)·β_k(y)·c_k(z)"""
    zi = POS.index(z)
    return sum(mul(mul(ALPHA[k][POS.index(x)], BETA[k][POS.index(y)]), C[k][zi])
               for k in range(7)) % 3


def matmul_entry(a, b, z):
    """(A·B)(z), a、b 为长度 4 的位置 → 值"""
    return sum(mul(a[(z[0], k)], b[(k, z[1])]) for k in range(2)) % 3


def strassen_entry(a, b, z):
    """Σ_k (α_k·A)(β_k·B)·c_k(z)"""
    zi = POS.index(z)
    return sum(mul(mul(dot(ALPHA[k], a), dot(BETA[k], b)), C[k][zi]) for k in range(7)) % 3


def check_structure_constants():
    """判据一: 64 个指标三元组"""
    tested = fires = 0
    for x, y, z in product(POS, repeat=3):
        tested += 1
        if struct_const(x, y, z) != tensor(x, y, z):
            fires += 1
            print("反例", x, y, z, struct_const(x, y, z), tensor(x, y, z))
    assert tested == 64 and fires == 0, (tested, fires)
    return tested


def check_matrices():
    """判据二: 6561 组输入 × 4 个输出, 走普通矩阵乘法"""
    tested = 0
    for vals in product(F3, repeat=8):
        a = dict(zip(POS, vals[:4]))
        b = dict(zip(POS, vals[4:]))
        for z in POS:
            tested += 1
            assert strassen_entry(a, b, z) == matmul_entry(a, b, z), (vals, z)
    assert tested == 6561 * 4, tested
    return tested


def check_two_paths_agree_on_basis():
    """两条路径在基矩阵上逐值一致（16 对 × 4 个输出 = 64 次比对）"""
    tested = 0
    for x, y in product(POS, repeat=2):
        ea = {p: (1 if p == x else 0) for p in POS}
        eb = {p: (1 if p == y else 0) for p in POS}
        for z in POS:
            tested += 1
            # 判据一路径: 结构常数
            v1 = struct_const(x, y, z)
            # 判据二路径: 把基矩阵喂给算法
            v2 = strassen_entry(ea, eb, z)
            # 普通矩阵乘法
            v3 = matmul_entry(ea, eb, z)
            assert v1 == v2 == v3, (x, y, z, v1, v2, v3)
    assert tested == 64, tested
    return tested


NAME = {(0, 0): "(fzero , fzero)", (0, 1): "(fzero , fsuc fzero)",
        (1, 0): "(fsuc fzero , fzero)", (1, 1): "(fsuc fzero , fsuc fzero)"}


def emit_clauses():
    """发射 64 条 refl 子句（按指标三元组; Agda 件未贴用, 见文件头说明）"""
    lines = []
    for x, y, z in product(POS, repeat=3):
        lines.append("basis-identity %s %s %s = refl" % (NAME[x], NAME[y], NAME[z]))
    return lines


import random


def check_span_construction(trials=400, seed=20261126):
    """M16-B: 在 Strassen 分解上检验「标准基 ⟹ 一切」的构造（n = 2, r = 7）"""
    rng = random.Random(seed)
    n, r = 2, 1
    pos4 = [(i, j) for i in range(2) for j in range(2)]
    assert len(pos4) == 4
    k = 0                                   # 固定的 k（行 / 列指标）

    def alpha(i, x):                        # i = 门, x = 位置 → 常数 α_i(x)
        return ALPHA[i][pos4.index(x)]

    def beta(i, y):
        return BETA[i][pos4.index(y)]

    def cc(i, z):
        return C[i][pos4.index(z)]

    # w x₀ i = β_i((x₀.2, k)) · c_i((x₀.1, k))
    def w(x0, i):
        return mul(beta(i, (x0[1], k)), cc(i, (x0[0], k)))

    def e(x0, x):
        return 1 if x0 == x else 0

    # (1) 标准基落在张成里: Σ_i w x₀ i · α_i(x) ≡ [x ≡ x₀]
    basis_fires = 0
    for x0 in pos4:
        for x in pos4:
            if sum(mul(w(x0, i), alpha(i, x)) for i in range(7)) % 3 == e(x0, x):
                basis_fires += 1
            else:
                raise AssertionError(("标准基不在张成里", x0, x))
    assert basis_fires == 16, basis_fires
    # (2) 任意 λ: t_λ i = Σ_{x₀} λ(x₀)·w x₀ i;  (Φ t_λ) x = Σ_i t_λ i · α_i(x) ≡ λ(x)
    fires = 0
    for _ in range(trials):
        lam = {x0: rng.randint(0, 2) for x0 in pos4}
        t = [sum(mul(lam[x0], w(x0, i)) for x0 in pos4) % 3 for i in range(7)]
        for x in pos4:
            if sum(mul(t[i], alpha(i, x)) for i in range(7)) % 3 == lam[x]:
                fires += 1
            else:
                raise AssertionError(("原像构造失败", lam, x))
    assert fires == trials * 4, (fires, trials)
    return basis_fires, fires


def check_span_capacity(samples=2000, seed=20261127):
    """M16-B: 张成容量 —— r < n² 装不下全部标准基; r ≥ n² 装得下（n = 2）"""
    rng = random.Random(seed)
    pos4 = [(i, j) for i in range(2) for j in range(2)]

    def in_span(a, r, v):
        # v 是否在 span{a_0..a_{r-1}} 里: 穷举系数 Trit^r
        for coeffs in product(F3, repeat=r):
            if all(sum(mul(coeffs[i], a[i][x]) for i in range(r)) % 3 == v[x] for x in pos4):
                return True
        return False

    def std(i):
        return {x: (1 if x == pos4[i] else 0) for x in pos4}

    tested = 0
    # r = 3 < 4: 随机生成元, 无一能张出全部 4 个标准基
    for _ in range(samples):
        r = 3
        a = [{x: rng.randint(0, 2) for x in pos4} for _ in range(r)]
        tested += 1
        assert not all(in_span(a, r, std(i)) for i in range(4)), a
    # 对照: 同一个判别器在 r = 4 时能报「在张成里」——否则上面的「无一成功」是空转
    r = 4
    a = [std(i) for i in range(r)]
    tested += 1
    cap_ok = sum(1 for i in range(4) if in_span(a, r, std(i)))
    assert cap_ok == 4, cap_ok
    # 计数判据: 3^(n²) ≤ 3^r ⟺ n² ≤ r
    for nn in range(0, 5):
        for rr in range(0, 12):
            tested += 1
            assert ((3 ** (nn * nn) <= 3 ** rr) == (nn * nn <= rr))
    return tested, samples, cap_ok


def kronecker(u, v):
    """两个 2×2 线性型(位置 → 系数)的张量积: 4×4 线性型(位置 → 系数), 位置 = 2·高 + 低"""
    out = {}
    for (p1, q1), c1 in zip(POS, u):
        for (p2, q2), c2 in zip(POS, v):
            out[(2 * p1 + p2, 2 * q1 + q2)] = mul(c1, c2)
    return out


def pos4():
    return [(p, q) for p in range(4) for q in range(4)]


def lo(x):
    """4×4 位置 → 低位 2×2 位置"""
    return (x[0] % 2, x[1] % 2)


def hi(x):
    """4×4 位置 → 高位 2×2 位置"""
    return (x[0] // 2, x[1] // 2)


def tensor4(x, y, z):
    """⟨4,4,4⟩ 的结构常数: [x.行 = z.行][x.列 = y.行][y.列 = z.列]"""
    return 1 if (x[0] == z[0] and x[1] == y[0] and y[1] == z[1]) else 0


def prod_tables():
    """Strassen ⊗ Strassen 的 49 项分解: 项 t = 7·i₁ + i₂; 三张表(项 × 位置)"""
    P4 = pos4()
    AA = [[mul(ALPHA[t // 7][POS.index(hi(x))], ALPHA[t % 7][POS.index(lo(x))]) for x in P4] for t in range(49)]
    BB = [[mul(BETA[t // 7][POS.index(hi(y))], BETA[t % 7][POS.index(lo(y))]) for y in P4] for t in range(49)]
    CC = [[mul(C[t // 7][POS.index(hi(z))], C[t % 7][POS.index(lo(z))]) for z in P4] for t in range(49)]
    return AA, BB, CC


def check_tensor_product():
    """M16-C 判据四: ⟨4,4,4⟩ 有 16 个位置, 全部 16³ = 4096 个结构常数三元组上
       Σ_t A t x · B t y · C t z ≡ T₂(x₁,y₁,z₁)·T₂(x₂,y₂,z₂) ≡ T₄(x,y,z)"""
    AA, BB, CC = prod_tables()
    P4 = pos4()
    idx = {x: i for i, x in enumerate(P4)}
    tested = fires = 0
    for x in P4:
        for y in P4:
            v = [mul(AA[t][idx[x]], BB[t][idx[y]]) for t in range(49)]
            for z in P4:
                lhs = sum(mul(v[t], CC[t][idx[z]]) for t in range(49)) % 3
                t2 = mul(tensor(hi(x), hi(y), hi(z)), tensor(lo(x), lo(y), lo(z)))
                t4 = tensor4(x, y, z)
                tested += 1
                if lhs == t2 == t4:
                    fires += 1
                else:
                    raise AssertionError(("张量积分解失败", x, y, z, lhs, t2, t4))
    assert tested == 16 * 16 * 16 and fires == tested, (tested, fires)
    return tested


def matmul4(a, b, z):
    """4×4 普通矩阵乘法的一个输出; a、b 为位置 → 值"""
    return sum(mul(a[(z[0], k)], b[(k, z[1])]) for k in range(4)) % 3


def check_tensor_product_matrices(trials=300, seed=20261129):
    """M16-C 判据五(独立路径): 随机 4×4 矩阵上, 49 项算法 ≡ 普通 4×4 矩阵乘法"""
    rng = random.Random(seed)
    P4 = pos4()
    forms = [kronecker(ALPHA[t // 7], ALPHA[t % 7]) for t in range(49)]
    formsB = [kronecker(BETA[t // 7], BETA[t % 7]) for t in range(49)]
    outs = [kronecker(C[t // 7], C[t % 7]) for t in range(49)]
    tested = 0
    for _ in range(trials):
        a = {x: rng.randint(0, 2) for x in P4}
        b = {x: rng.randint(0, 2) for x in P4}
        u = [sum(mul(forms[t][x], a[x]) for x in P4) % 3 for t in range(49)]
        w = [sum(mul(formsB[t][y], b[y]) for y in P4) % 3 for t in range(49)]
        for z in P4:
            tested += 1
            lhs = sum(mul(mul(u[t], w[t]), outs[t][z]) for t in range(49)) % 3
            assert lhs == matmul4(a, b, z), (a, b, z)
    assert tested == trials * 16
    return tested


def check_rank_one_and_certificate():
    """M16-C: ⟨1⟩ 的 1 项分解(全 1 系数); 有限证书 7^6 ≤ 2^17 及其各次幂"""
    tested = 0
    # ⟨1⟩: a = b = c = 1, Σ = 1·(1·1) = T(·,·,·) = 1
    assert tensor((0, 0), (0, 0), (0, 0)) == 1 == 1 * (1 * 1) % 3
    tested += 1
    assert 7 ** 6 == 117649 and 2 ** 17 == 131072
    assert 7 ** 6 <= 2 ** 17
    tested += 2
    for k in range(0, 8):
        tested += 1
        assert (7 ** k) ** 6 <= (2 ** k) ** 17, k
    # 对照: 更紧的 7^5 ≤ 2^14 是**假**的(16807 > 16384)——证书的分母 6 不能换成 5
    assert 7 ** 5 > 2 ** 14
    tested += 1
    return tested


def check_savings(pmax=12, samples=3000, seed=20261130):
    """M16-D: 严格节省的两条算术（整数幂, Python 大整数）"""
    rng = random.Random(seed)
    tested = 0
    # (1) Strassen 覆盖 p/q >= 17/6
    for q in range(1, pmax + 1):
        p0 = (17 * q + 5) // 6                      # ceil(17q / 6)
        for p in range(p0, p0 + 30):
            tested += 1
            assert (7 ** (6 * q)) ** q < (2 ** (6 * q)) ** p, (p, q)
    # (1b) 对照: 17/6 之下（p = p0 - 1 且 17(q+1)… 取 9/4 < p/q < 17/6 的比值）不成立——证书的 17/6 不能再降
    for (p, q) in ((13, 5), (14, 5), (19, 7), (24, 9)):      # 都严格落在 9/4 与 17/6 之间
        assert 9 * q < 4 * p and 17 * q > 6 * p, (p, q)
        tested += 1
        assert not (7 ** (6 * q)) ** q < (2 ** (6 * q)) ** p, (p, q)
    # (2) 不重叠: 下半 + 节省 ⟹ 9q < 4p
    fires = 0
    for _ in range(samples):
        n = rng.randint(2, 40)
        lo = 1
        while lo ** 4 < n ** 9:
            lo += 1
        r = rng.randint(lo, lo + 200)               # n^9 <= r^4
        assert n ** 9 <= r ** 4
        tested += 1
        for q in range(1, 7):
            for p in range(1, 14):
                if r ** q < n ** p:
                    fires += 1
                    assert 9 * q < 4 * p, (n, r, p, q)
    assert fires > 0, fires
    # 负对照: 去掉下半前提, 蕴含不成立
    tested += 1
    assert 2 ** 9 > 1 ** 4 and 1 ** 1 < 2 ** 1 and not (9 * 1 < 4 * 1)
    return tested, fires


def main():
    n1 = check_structure_constants()
    n2 = check_matrices()
    n3 = check_two_paths_agree_on_basis()
    print("判据一 (结构常数, 64 个指标三元组): %d 次全部成立" % n1)
    print("判据二 (6561 组输入 × 4 输出, 普通矩阵乘法): %d 次全部成立" % n2)
    print("两路会合 (16 对基矩阵 × 4 输出): %d 次逐值一致" % n3)
    basis4, fires4 = check_span_construction()
    tested5, cap_fires, cap_ok = check_span_capacity()
    print("M16-B 张成构造 (Strassen 分解): 标准基落在张成里 %d/16; 原像复原 %d/1600" % (basis4, fires4))
    print("M16-B 张成容量 (r = 3 的 %d 组随机生成元无一张出全部标准基; 对照 r = 4: 标准基 %d/4 在张成里; 计数判据): %d 次核对"
          % (cap_fires, cap_ok, tested5))
    n6 = check_tensor_product()
    n7 = check_tensor_product_matrices()
    n8 = check_rank_one_and_certificate()
    print("M16-C 张量积分解 (Strassen⊗Strassen = ⟨4,4,4⟩ 49 项): 结构常数 %d/4096; 随机 4×4 矩阵独立路径 %d/%d"
          % (n6, n7, 300 * 16))
    print("M16-C rank-one + 有限证书 7^6 ≤ 2^17 (及 (7^k)^6 ≤ (2^k)^17, k ≤ 7): %d 次核对" % n8)
    n9, f9 = check_savings()
    print("M16-D 严格节省: %d 次核对; 其中「下半 + 节省 ⟹ 9q < 4p」的蕴含实际触发 %d 次" % (n9, f9))
    # 与 M13 头注一致的账本: 恰 7 项
    assert len(ALPHA) == len(BETA) == len(C) == 7
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w", encoding="utf-8") as fh:
            fh.write("\n".join(emit_clauses()) + "\n")
        print("已发射 64 条 refl 子句 →", sys.argv[1])
    print("TensorRankGF3 oracle: ALL_PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
