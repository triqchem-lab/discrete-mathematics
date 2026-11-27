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
M23 / M24（TensorRankAlgebraGF3 / TensorRankHK2GF3）: Hopcroft–Kerr 的 2×2 排除论证 —— 数值核对与分类表生成
  · forced product 的残差: 四个权重对全部 6561 组 (u,v) 给出 δ₂, δ₃, −δ₀, −δ₁; 负对照（漏一项即出错）
  · 超平面分类: 80 个非零泛函各一对 (P,Q) 见证, 四条恒等式（含 Agda 里重排后的 move 形状）逐条核对
  · 端到端: Strassen 的 7 项各当一次 i₀, 限制 → 搬到 K → 两次规范化 → 残差权重, 全部对上
  · --hk2-table [路径]: 重新生成 Agda 件里的分类表; 缺省运行时与库内那张表逐字对账
禁浮点; 全部是 GF(3) 上的整数运算。
"""
import os
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


# ---------------------------------------------------------------------------
# M22（TensorRankIndexGF3）: 指标集泛型谓词的四条结构引理 —— 数值核对
#   把 Pos 2 的 4 个位置看作 X = Fin 4（下标 = POS 的序号）, Strassen 分解 = (α, β, 输出系数)。
#   Agda 的「分解」是三张系数表 a : Fin r → X → Trit … 加恒等式 Σ_i a i x ⊗ (b i y ⊗ c i z) ≡ T x y z;
#   下面每条判据都与 Agda 的陈述逐字对应, 用随机输入核对恒等式本身, 不只是核对结论「存在分解」。
# ---------------------------------------------------------------------------
import random as _random


def decomp_value(A, B, Cf, x, y, z):
    """Σ_i a i x ⊗ (b i y ⊗ c i z) —— 对应 Agda 的 sumFin (λ i → ra i x ⊗ (rb i y ⊗ (rc i z)))"""
    return sum(mul(A[k][x], mul(B[k][y], Cf[k][z])) for k in range(len(A))) % 3


def m22_tables():
    """Strassen 分解写成 Fin 4 上的三张表: a i x = α_i(x), b i y = β_i(y), c i z = 输出系数(POS 序号)"""
    A = [[ALPHA[k][x] for x in range(4)] for k in range(7)]
    B = [[BETA[k][y] for y in range(4)] for k in range(7)]
    Cf = [[C[k][z] for z in range(4)] for k in range(7)]
    T = lambda x, y, z: tensor(POS[x], POS[y], POS[z])
    return A, B, Cf, T


def check_m22_pull():
    """rank-pull: 对全部 4³ = 64 个映射 g : Fin 3 → Fin 4, 拉回后的分解给出 T(g x', y, z)"""
    A, B, Cf, T = m22_tables()
    n = ok = 0
    for gt in product(range(4), repeat=3):
        g = list(gt)
        for x1, y, z in product(range(3), range(4), range(4)):
            n += 1
            if decomp_value([[a[g[i]] for i in range(3)] for a in A], B, Cf, x1, y, z) == T(g[x1], y, z):
                ok += 1
    return n, ok


def check_m22_invar(trials=6, seed=20261201):
    """rank-invar: g 是 Fin 4 的置换、h = g⁻¹ 时, 先沿 g 拉回再沿 h 搬回, 得到原分解 (64 个三元组逐一相等)。
    负对照: g 不是置换时, 对全部 4⁴ = 256 个 h 没有一个能把恒等式恢复。"""
    A, B, Cf, T = m22_tables()
    rnd = _random.Random(seed)
    n = ok = 0
    perms = list(range(4))
    for _ in range(trials):
        rnd.shuffle(perms)
        g = perms[:]                      # g : Fin 4 → Fin 4
        h = [0] * 4
        for x in range(4):
            h[g[x]] = x
        Ag = [[a[g[i]] for i in range(4)] for a in A]       # 沿 g 拉回后的分解
        Agh = [[a[h[i]] for i in range(4)] for a in Ag]      # 沿 h 搬回
        for x, y, z in product(range(4), repeat=3):
            n += 1
            if decomp_value(Agh, B, Cf, x, y, z) == T(x, y, z):
                ok += 1
    # 负对照: g = (0, 0, 2, 3) 不是置换
    g = [0, 0, 2, 3]
    Ag = [[a[g[i]] for i in range(4)] for a in A]
    fixed = 0
    for ht in product(range(4), repeat=4):
        Agh = [[a[ht[i]] for i in range(4)] for a in Ag]
        if all(decomp_value(Agh, B, Cf, x, y, z) == T(x, y, z) for x, y, z in product(range(4), repeat=3)):
            fixed += 1
    return n, ok, fixed


def check_m22_restrict(trials=400, seed=20261202):
    """rank-restrict: 随机 s : Fin k → Fin 4 (k = 1..5),
       Σ_i (Σ_x s j x ⊗ a i x) ⊗ (b i y ⊗ c i z) ≡ Σ_x s j x ⊗ T x y z 对全部 (j, y, z) 成立。
       独立路径(意义): 第一变元取 v = s[0] 时, 三线性型 Σ_{xyz} v_x·T(x,y,z)·w_y·u_z
       等于 Σ_{ik} (V·W)_{ik}·U_{ik} —— 走普通矩阵乘法, 不经恒等式。
       负对照: s = 2·e_{x₀}(单位向量的 2 倍)时, 限制值 = 2·T(x₀,y,z) ≠ T(x₀,y,z), 只要 T(x₀,y,z) = 1(共 8 处)。"""
    A, B, Cf, T = m22_tables()
    rnd = _random.Random(seed)

    def restricted(s, i):
        """a 复合 s 之后的系数: Σ_x s x ⊗ a i x"""
        return [sum(mul(s[x], A[i][x]) for x in range(4)) % 3 for _ in (0,)][0]

    n = ok = sem_n = sem_ok = neg_fire = 0
    for _ in range(trials):
        k = rnd.randint(1, 5)
        s = [[rnd.randint(0, 2) for _ in range(4)] for _ in range(k)]
        a_s = [[restricted(s[j], i) for j in range(k)] for i in range(7)]
        for j, y, z in product(range(k), range(4), range(4)):
            n += 1
            lhs = decomp_value(a_s, B, Cf, j, y, z)
            rhs = sum(mul(s[j][x], T(x, y, z)) for x in range(4)) % 3
            if lhs == rhs:
                ok += 1
        for _ in range(3):
            V = s[0]                                              # Fin 4 上的坐标(顺序同 POS)
            W = [rnd.randint(0, 2) for _ in range(4)]
            U = [rnd.randint(0, 2) for _ in range(4)]
            L = sum(mul(mul(V[x], T(x, y, z)), mul(W[y], U[z]))
                    for x, y, z in product(range(4), repeat=3)) % 3
            Vd = {POS[i]: V[i] for i in range(4)}               # matmul_entry 要的是 位置 → 值
            Wd = {POS[i]: W[i] for i in range(4)}
            R = sum(mul(matmul_entry(Vd, Wd, POS[i]), U[i]) for i in range(4)) % 3
            sem_n += 1
            if L == R:
                sem_ok += 1
    for x0, y, z in product(range(4), repeat=3):
        s2 = [2 if x == x0 else 0 for x in range(4)]
        a_s = [[restricted(s2, i)] for i in range(7)]
        lhs = decomp_value(a_s, B, Cf, 0, y, z)
        if T(x0, y, z) == 1 and lhs != T(x0, y, z):
            neg_fire += 1
    return n, ok, sem_n, sem_ok, neg_fire


def check_m22_sym():
    """rank-swap / rank-rot: 交换 a 与 b(或轮回 (b, c, a))之后恒等式仍成立"""
    A, B, Cf, T = m22_tables()
    n = ok_swap = ok_rot = 0
    for x, y, z in product(range(4), repeat=3):
        n += 1
        if decomp_value(B, A, Cf, y, x, z) == T(x, y, z):
            ok_swap += 1
        lhs = sum(mul(B[k][y], mul(Cf[k][z], A[k][x])) for k in range(7)) % 3
        if lhs == T(x, y, z):
            ok_rot += 1
    return n, ok_swap, ok_rot


# ---------------------------------------------------------------------------
# M23 / M24（TensorRankAlgebraGF3 / TensorRankHK2GF3）: Hopcroft–Kerr 的 2×2 排除论证 —— 数值核对
#   证明链（Agda 件 TensorRankHK2GF3.rank-2x2-lower: ∀ r → RankLE₃ 2 r → 7 ≤ r）:
#     ① ⟨2,2,2⟩ 有 r 项分解, 取第一系数非零的一项 i₀, 把第一变元限制到 ker(ra i₀) 并丢掉第 i₀ 项
#        ⟹ 子空间 W 上的张量有 r − 1 项分解。
#     ② 每个非零泛函 ℓ 的核里都有一个「K 型」子空间 W: 80 个泛函各给一对可逆的 (P, Q),
#        W_j = P⁻¹·κ_j·Q（κ = J, E₂₂; K = span{J, E₂₂}）; 分解沿 (A, cA), (B, cB) 搬到 K 上。
#     ③ K 上的张量用 forced product: c₀₀ 与 c₀₁ 两个切片是单个的积, 两次切片规范化后余项有 r − 3 项,
#        余项的 y-切片张成 4 维 ⟹ 4 ≤ r − 3。
#   下面每条判据都是这条链的一环的独立实现（矩阵走普通乘法, 不经 Agda 的恒等式）。
#   坐标: Fin 4 = 行主序 POS; 矩阵 = 行主序 4 元组 (a, b, c, d) = [[a, b],[c, d]]。
# ---------------------------------------------------------------------------
HK2_AGDA = os.path.normpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "src",
                                         "Sovereign", "Algebra", "LinearAlgebra", "TensorRankHK2GF3.agda"))
HK2_BEGIN = "-- BEGIN hk2-table —— 由 engineering/oracle_tensor_rank_gf3.py --hk2-table 生成, 勿手改"
HK2_END = "-- END hk2-table"
TRIT_NAME = ("T₀", "T₁", "T₂")

HK2_J = (0, 1, 2, 0)                  # [[0,1],[-1,0]]
HK2_E22 = (0, 0, 0, 1)
HK2_KAPPA = (HK2_J, HK2_E22)          # K = span{J, E₂₂} 的基
HK2_SK = ((0, 1, 2, 0), (0, 0, 0, 1))  # 同一组基在 Fin 4 上的坐标行
HK2_F = (1, 0)                        # f x = [x = a]
HK2_I2 = (1, 0, 0, 1)


def hk2_mm(a, b):
    return (add(mul(a[0], b[0]), mul(a[1], b[2])),
            add(mul(a[0], b[1]), mul(a[1], b[3])),
            add(mul(a[2], b[0]), mul(a[3], b[2])),
            add(mul(a[2], b[1]), mul(a[3], b[3])))


def hk2_det(a):
    return add(mul(a[0], a[3]), neg(mul(a[1], a[2])))


def hk2_inv(a):
    """adj / det（det = 0 时返回全零, 对应 Agda 的 TritInv T₀ = T₀）"""
    d = hk2_det(a)
    di = 0 if d == 0 else (1 if d == 1 else 2)
    return (mul(di, a[3]), neg(mul(di, a[1])), neg(mul(di, a[2])), mul(di, a[0]))


def hk2_tr(a):
    return (a[0], a[2], a[1], a[3])


def hk2_row(k):
    return k // 2


def hk2_col(k):
    return k % 2


def hk2_e(m, r, c):
    return m[2 * r + c]


def hk2_t4(p, y, z):
    """坐标化的结构常数 T4(p,y,z) = mm 2 (unpos p) (unpos y) (unpos z)"""
    return tensor(POS[p], POS[y], POS[z])


def hk2_tk(j, y, z):
    """K 上的张量 TK j y z = Σ_p sK j p ⊗ T4 p y z"""
    return sum(mul(HK2_SK[j][p], hk2_t4(p, y, z)) for p in range(4)) % 3


def hk2_delta(i, y):
    return 1 if i == y else 0


def hk2_R(u, v, x, y, z):
    """forced product 两次规范化后的残差: TK ⊕ −f⊗(g⊗u) ⊕ −f⊗(g'⊗v)（g = δ₂, g' = δ₃）"""
    return (hk2_tk(x, y, z)
            + neg(mul(HK2_F[x], mul(hk2_delta(2, y), u[z])))
            + neg(mul(HK2_F[x], mul(hk2_delta(3, y), v[z])))) % 3


def hk2_W(lam, u, v, y):
    """y-切片的线性组合: Σ_x Σ_z λ x z ⊗ R(x,y,z)"""
    return sum(mul(lam[x][z], hk2_R(u, v, x, y, z)) for x in range(2) for z in range(4)) % 3


def hk2_weights(u, v):
    """四个权重: 组合出来恰是 δ₂, δ₃, −δ₀, −δ₁（与 u, v 无关）"""
    l1 = [[0, 0, 0, 0], [0, 0, 1, 0]]
    l2 = [[0, 0, 0, 0], [0, 0, 0, 1]]
    l3 = [[0, 0, 1, 0], [0, 0, u[2], v[2]]]
    l4 = [[0, 0, 0, 1], [0, 0, u[3], v[3]]]
    return (l1, l2, l3, l4)


HK2_EXPECT = ((0, 0, 1, 0), (0, 0, 0, 1), (2, 0, 0, 0), (0, 2, 0, 0))


def check_hk2_residual():
    """对全部 3⁴×3⁴ = 6561 组 (u, v): 四个权重的组合恰是 δ₂, δ₃, −δ₀, −δ₁。
    负对照: λ₃ 去掉 v[2] 那一项后, 在 y = 3 处出错（首版手算就漏了这一项, 由本判据抓到）。"""
    n = ok = 0
    for ut in product(F3, repeat=4):
        for vt in product(F3, repeat=4):
            u, v = list(ut), list(vt)
            for k, lam in enumerate(hk2_weights(u, v)):
                n += 1
                if tuple(hk2_W(lam, u, v, y) for y in range(4)) == HK2_EXPECT[k]:
                    ok += 1
    bad = 0
    for ut in product(F3, repeat=4):
        for vt in product(F3, repeat=4):
            u, v = list(ut), list(vt)
            l3 = [[0, 0, 1, 0], [0, 0, u[2], 0]]
            if hk2_W(l3, u, v, 3) != 0:
                bad += 1
    return n, ok, bad


def hk2_wit_data(P, Q):
    """见证的数据: 由 (P, Q) 算出 W 的两行与两组换元矩阵。
       A[k][w] = (Q⁻¹)[k行][w行]·[k列 = w列];  cA[w][k] = Q[w行][k行]·[同列]
       B[k][w] = P[w行][k行]·[同列];            cB[w][k] = (P⁻ᵀ)[w行][k行]·[同列]"""
    Pi = hk2_inv(P)
    Qi = hk2_inv(Q)
    PiT = hk2_tr(Pi)
    rows = tuple(tuple(hk2_mm(hk2_mm(Pi, HK2_KAPPA[j]), Q)[p] for p in range(4)) for j in range(2))
    same = lambda k, w: hk2_col(k) == hk2_col(w)
    A = [[hk2_e(Qi, hk2_row(k), hk2_row(w)) if same(k, w) else 0 for w in range(4)] for k in range(4)]
    cA = [[hk2_e(Q, hk2_row(w), hk2_row(k)) if same(k, w) else 0 for k in range(4)] for w in range(4)]
    B = [[hk2_e(P, hk2_row(w), hk2_row(k)) if same(k, w) else 0 for w in range(4)] for k in range(4)]
    cB = [[hk2_e(PiT, hk2_row(w), hk2_row(k)) if same(k, w) else 0 for k in range(4)] for w in range(4)]
    return rows, A, cA, B, cB


def hk2_wit_ok(P, Q, l):
    """四条恒等式: ℓ 在 W 上恒零; cA·A = I; cB·B = I; T(W_j, y, z) = Σ A[k][y]·B[k'][z]·TK(j,k,k')"""
    rows, A, cA, B, cB = hk2_wit_data(P, Q)
    for j in range(2):
        if sum(mul(rows[j][p], l[p]) for p in range(4)) % 3 != 0:
            return False
    for k in range(4):
        for k0 in range(4):
            if sum(mul(cA[w][k0], A[k][w]) for w in range(4)) % 3 != hk2_delta(k, k0):
                return False
            if sum(mul(cB[w][k0], B[k][w]) for w in range(4)) % 3 != hk2_delta(k, k0):
                return False
    for j, y, z in product(range(2), range(4), range(4)):
        tw = sum(mul(rows[j][p], hk2_t4(p, y, z)) for p in range(4))
        rhs = sum(mul(A[k][y], mul(B[kp][z], hk2_tk(j, k, kp))) for k in range(4) for kp in range(4))
        if tw % 3 != rhs % 3:
            return False
        # Agda 件 Good.move 里写的是先对 k 求和的形状: Σ_{k'} B[k'][z]·Σ_k A[k][y]·TK(j,k,k')
        rhs2 = sum(mul(B[kp][z], sum(mul(A[k][y], hk2_tk(j, k, kp)) for k in range(4))) for kp in range(4))
        if tw % 3 != rhs2 % 3:
            return False
    return True


def hk2_classify_all():
    """80 个非零泛函各找一对 (P, Q)。优先复用已用过的对, 让表更短。
    返回 {ℓ: (P, Q)}、试探次数、负对照计数、ℓ 的矩阵秩 1 的泛函个数（断言 32; 只是计数, 不是「两个轨道」的证明）。"""
    gl = [m for m in product(F3, repeat=4) if hk2_det(m) != 0]
    assert len(gl) == 48
    table = {}
    used = []
    tried = 0
    for lt in product(F3, repeat=4):
        if lt == (0, 0, 0, 0):
            continue
        found = None
        for P, Q in used + [(P, Q) for P in gl for Q in gl]:
            tried += 1
            if hk2_wit_ok(P, Q, lt):
                found = (P, Q)
                break
        assert found is not None, lt
        if found not in used:
            used.append(found)
        table[lt] = found
    wrong = sum(1 for lt in table if not hk2_wit_ok(HK2_I2, HK2_I2, lt))
    # 计数（不是「两个轨道」的证明）: ℓ 的矩阵秩 1 的 32 个, 可逆的 48 个
    rank1 = sum(1 for lt in table if hk2_det(lt) == 0)
    assert rank1 == 32 and len(table) - rank1 == 48, (rank1, len(table) - rank1)
    return table, tried, wrong, rank1


def hk2_normalize(T, c, f, g, A, B, Cf):
    """slice-normalize 的构造（镜像 Agda）: T(x,y,c) ≡ f x ⊗ g y; 取第一个 rc i c ≠ 0 的项 i₀;
       w = (rc i₀ c)⁻¹·rc i₀; 其余项 rc' i z = rc i z ⊕ −((rc i c ⊗ ki) ⊗ rc i₀ z); 去掉 i₀。"""
    r = len(A)
    i0 = next(i for i in range(r) if Cf[i][c] != 0)
    k = Cf[i0][c]
    ki = 1 if k == 1 else 2
    w = [mul(ki, Cf[i0][z]) for z in range(4)]
    assert w[c] == 1
    keep = [i for i in range(r) if i != i0]
    A2 = [A[i] for i in keep]
    B2 = [B[i] for i in keep]
    C2 = [[add(Cf[i][z], neg(mul(mul(Cf[i][c], ki), Cf[i0][z]))) for z in range(4)] for i in keep]
    return w, A2, B2, C2


def check_hk2_end_to_end(table):
    """用 Strassen 的真实 7 项分解, 让每一项各当一次 i₀: ℓ = α_{i₀} 非零 ⇒ 见证 ⇒ T_W 有 6 项分解
       ⇒ 搬到 K 仍是分解 ⇒ 两次规范化后余项有 4 项分解, 且恰等于残差 R(u, v) ⇒ 四个权重给出 δ。"""
    n = ok_restr = ok_transfer = ok_res = ok_w = 0
    for i0 in range(7):
        l = ALPHA[i0]
        P, Q = table[tuple(l)]
        rows, A, cA, B, cB = hk2_wit_data(P, Q)
        keep = [i for i in range(7) if i != i0]
        As = [[sum(mul(rows[j][p], ALPHA[i][p]) for p in range(4)) % 3 for j in range(2)] for i in keep]
        Bs = [BETA[i] for i in keep]
        Cs = [C[i] for i in keep]
        n += 1
        # 丢掉的那一项在 W 上恒零
        assert all(sum(mul(rows[j][p], l[p]) for p in range(4)) % 3 == 0 for j in range(2))
        ok_restr += all(decomp_value(As, Bs, Cs, j, y, z) == sum(mul(rows[j][p], hk2_t4(p, y, z)) for p in range(4)) % 3
                        for j, y, z in product(range(2), range(4), range(4)))
        # 搬到 K: b' i k₀ = Σ_w cA[w][k₀]·b i w;  c' i k₀ = Σ_w cB[w][k₀]·c i w
        Bt = [[sum(mul(cA[w][k0], Bs[i][w]) for w in range(4)) % 3 for k0 in range(4)] for i in range(6)]
        Ct = [[sum(mul(cB[w][k0], Cs[i][w]) for w in range(4)) % 3 for k0 in range(4)] for i in range(6)]
        ok_transfer += all(decomp_value(As, Bt, Ct, j, k0, kp) == hk2_tk(j, k0, kp)
                           for j, k0, kp in product(range(2), range(4), range(4)))
        # 两次规范化: c₀₀ 切片 f⊗g (g = δ₂), c₀₁ 切片 f⊗g'' (g'' = g' ⊕ −(w₀₁·g))
        g = [hk2_delta(2, y) for y in range(4)]
        g1 = [hk2_delta(3, y) for y in range(4)]
        w0, A1, B1, C1 = hk2_normalize(hk2_tk, 0, HK2_F, g, As, Bt, Ct)
        gp = [add(g1[y], neg(mul(w0[1], g[y]))) for y in range(4)]
        assert gp[3] == 1
        w1, A2, B2, C2 = hk2_normalize(hk2_tk, 1, HK2_F, gp, A1, B1, C1)
        assert len(A2) == 4
        # 余项 = TK ⊕ −f⊗g'⊗w₁ ⊕ −f⊗g⊗(w₀ − w₀₁·w₁)
        #    = TK ⊕ −f⊗g⊗w₀ ⊕ −f⊗g''⊗w₁,  g'' = g' ⊕ −(w₀₁·g)
        #    = TK ⊕ −f⊗g'⊗w₁ ⊕ −f⊗g⊗(w₀ − w₀₁·w₁)   (首版把 u 写成 w₀ + w₀₁·w₁, 7 个里错 4 个)
        u = [add(w0[z], neg(mul(w0[1], w1[z]))) for z in range(4)]
        v = w1
        ok_res += all(decomp_value(A2, B2, C2, x, y, z) == hk2_R(u, v, x, y, z)
                      for x, y, z in product(range(2), range(4), range(4)))
        ok_w += all(tuple(hk2_W(lam, u, v, y) for y in range(4)) == HK2_EXPECT[q]
                    for q, lam in enumerate(hk2_weights(u, v)))
    return n, ok_restr, ok_transfer, ok_res, ok_w


def hk2_mat_lit(m):
    return "(mkMat2 %s)" % " ".join(TRIT_NAME[c] for c in m)


def emit_hk2_table(table):
    """Agda 的 hyper-wit 子句: 每个非零泛函一行; 见证的四条恒等式由内核归约核对（mkW … tt）。"""
    lines = []
    for lt in sorted(table):
        P, Q = table[lt]
        lits = " ".join(TRIT_NAME[c] for c in lt)
        lines.append("hyper-wit %s _ = mkW %s %s %s tt" % (lits, hk2_mat_lit(P), hk2_mat_lit(Q), lits))
    lines.append("hyper-wit T₀ T₀ T₀ T₀ h = ⊥-elim (nz-elim h)")
    return HK2_BEGIN + "\n" + "\n".join(lines) + "\n" + HK2_END + "\n"


def hk2_table_block(path):
    """取出 Agda 件里两个标记之间的块（含标记）; 没有标记返回 None"""
    if not os.path.exists(path):
        return None
    s = open(path, encoding="utf-8").read()
    i, j = s.find(HK2_BEGIN), s.find(HK2_END)
    if i < 0 or j < 0 or j < i:
        return None
    return s[i:j + len(HK2_END) + 1]


def write_hk2_table(path, text):
    old = hk2_table_block(path)
    assert old is not None, "%s 缺少标记 %s / %s" % (path, HK2_BEGIN, HK2_END)
    s = open(path, encoding="utf-8").read()
    open(path, "w", encoding="utf-8").write(s.replace(old, text, 1))
    print("分类表已重新生成 → %s（%d 行）" % (path, text.count("\n") - 2))


def verify_hk2_table(path, text):
    old = hk2_table_block(path)
    if old is None:
        return False, "缺标记块"
    if old == text:
        return True, "%d 行逐字一致" % (text.count("\n") - 2)
    ol, nl = old.split("\n"), text.split("\n")
    diff = [i for i, (x, y) in enumerate(zip(ol, nl)) if x != y]
    return False, "有 %d 行不一致（首处在第 %d 行）" % (len(diff) + abs(len(ol) - len(nl)), (diff[0] if diff else min(len(ol), len(nl))))


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
    p_n, p_ok = check_m22_pull()
    i_n, i_ok, i_fixed = check_m22_invar()
    r_n, r_ok, rs_n, rs_ok, r_neg = check_m22_restrict()
    s_n, s_swap, s_rot = check_m22_sym()
    print("M22 rank-pull (全部 64 个 g : Fin 3 → Fin 4 × 48 个三元组): %d/%d" % (p_ok, p_n))
    print("M22 rank-invar (置换 g 与 g⁻¹: 先拉回再搬回 = 原分解) %d/%d; 负对照: 非置换 g 时能把恒等式恢复的 h 有 %d 个(应为 0)"
          % (i_ok, i_n, i_fixed))
    print("M22 rank-restrict (随机 s, 恒等式) %d/%d; 三线性型意义(普通矩阵乘法独立路径) %d/%d; "
          "负对照(s = 2·e_{x₀}: 限制值 = 2·T(x₀,y,z) ≠ T(x₀,y,z), 应为 8 次) %d 次" % (r_ok, r_n, rs_ok, rs_n, r_neg))
    print("M22 rank-swap / rank-rot (64 个三元组): %d/%d, %d/%d" % (s_swap, s_n, s_rot, s_n))
    # M23 / M24: Hopcroft–Kerr 的 2×2 排除论证
    hk_n, hk_ok, hk_bad = check_hk2_residual()
    hk_tab, hk_tried, hk_wrong, hk_rank1 = hk2_classify_all()
    hk_e = check_hk2_end_to_end(hk_tab)
    print("M24 forced product 残差: 四个权重给出 δ₂, δ₃, −δ₀, −δ₁ —— %d/%d (6561 组 (u,v) × 4); "
          "负对照(λ₃ 漏掉 v₂·δ(d,3): 在 y = 3 处出错) %d 组"
          % (hk_ok, hk_n, hk_bad))
    print("M24 超平面分类: 80 个非零泛函 %d 个有 (P,Q) 见证(共试探 %d 对, 实际用到 %d 对); "
          "负对照((P,Q) = (I,I) 对多少个泛函不成立) %d 个; 计数: ℓ 的矩阵秩 1 的 %d 个、可逆的 %d 个"
          "(只是计数, 不是「两个轨道」的证明)"
          % (len(hk_tab), hk_tried, len(set(hk_tab.values())), hk_wrong, hk_rank1, len(hk_tab) - hk_rank1))
    print("M24 端到端(Strassen 的 7 项各当一次 i₀): 限制 %d/%d, 搬到 K %d/%d, 两次规范化后的残差 %d/%d, 残差权重 %d/%d"
          % (hk_e[1], hk_e[0], hk_e[2], hk_e[0], hk_e[3], hk_e[0], hk_e[4], hk_e[0]))
    # 先算后验纪律: 前提成立数必须 > 0, 否则上面的「全部成立」是空转
    assert p_n == 64 * 3 * 16 and p_ok == p_n
    assert i_n > 0 and i_ok == i_n and i_fixed == 0
    assert r_n > 0 and r_ok == r_n and rs_n > 0 and rs_ok == rs_n and r_neg == 8
    assert s_n == 64 and s_swap == s_rot == 64
    assert hk_n == 6561 * 4 and hk_ok == hk_n and hk_bad > 0
    assert len(hk_tab) == 80 and hk_wrong > 0
    assert hk_e[0] == 7 and hk_e[1] == hk_e[2] == hk_e[3] == hk_e[4] == 7
    # 与 M13 头注一致的账本: 恰 7 项
    assert len(ALPHA) == len(BETA) == len(C) == 7
    # 分类表: 与 Agda 件里的生成块对账 / 重新生成
    if "--hk2-table" in sys.argv:
        i = sys.argv.index("--hk2-table")
        tgt = sys.argv[i + 1] if len(sys.argv) > i + 1 else HK2_AGDA
        text = emit_hk2_table(hk_tab)
        if tgt == "-":
            sys.stdout.write(text)
        else:
            write_hk2_table(tgt, text)
        return 0
    if os.path.exists(HK2_AGDA):
        same, msg = verify_hk2_table(HK2_AGDA, emit_hk2_table(hk_tab))
        print("M24 分类表对账(%s): %s" % (os.path.basename(HK2_AGDA), msg))
        assert same
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w", encoding="utf-8") as fh:
            fh.write("\n".join(emit_clauses()) + "\n")
        print("已发射 64 条 refl 子句 →", sys.argv[1])
    print("TensorRankGF3 oracle: ALL_PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
