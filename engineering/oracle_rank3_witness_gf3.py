#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""oracle_rank3_witness_gf3.py — M17: GF(3) 上 ⟨3,3,3⟩ 的 23 项秩分解见证（Laderman-23）

来源: GitHub `RakTikoo/matmul-333-tensor-rank` 的机器可读证书（2026-11-26 经代理取回,
本文件嵌入原值; 取回后先经 /tmp 丢弃式脚本验证再入库）:
  - LAD = laderman_r23_Q.json   —— Laderman 1976 的 23 门方案
  - PER = perminov_cn122_r23_Q.json —— Perminov CN-122（同秩 23, 加法更少）
两份证书系数全 ∈ {-1,0,1}（纯整数）, 故 ℤ 上成立 ⟹ 对任意交换环成立, GF(3) 是实例。

约定（与库内 `mm` 逐字对齐, `TensorRankGF3.agda:82`）:
  x,y,z ∈ {0..8} 按行主序读成 Fin 3 × Fin 3 的（行,列）;
  mm(x,y,z) = [x_r = z_r][x_c = y_r][y_c = z_c]  —— 即 Σ A_ij·B_jk·C_ik 的系数张量;
  u_k(x) = U[x][k], v_k(y) = V[y][k], w_k(z) = W[z][k], k = 0..22。

判据（每条打印并断言前提火计, 不许空转）:
  1. 结构常数: 729 个 (x,y,z) 里恰 27 个非零
  2. Laderman-23 在 GF(3) 上 729/729 逐点成立; 27 个非零目标全命中; 23 门每门 u,v,w 全非零
  3. 同一证书在 ℤ 上 729/729（整数恒等式 ⟹ 域无关）
  4. Perminov-23 在 GF(3) 上 729/729（第二份独立方案）
  5. 负控制 ×3: 改 U 一个系数 / 改 W 一个系数 / 改一个结构常数, 判据必须转红
  6. GF(3) 上 23 个秩一贡献 u_k⊗v_k⊗w_k 线性无关（Gauss 消元 rank = 23）
     ⇒ 丢弃任何一门都不再是分解（有界否定数据点, 纯机器可核）
  7. 阈值事实（纯整数, 无浮点）:
     - 23^7 < 3^20 ⇒ (3,23) 见证给出 ω₃ ≤ 20/7;
     - 23^6 > 3^17 ⇒ 对一切 p,q: 6p < 17q 时 23^q < 3^p 不可能 —— (3,23) 从不越过 17/6
       （这正是 Agda 件 `laderman-not-below` 的数值内容）;
     - n=3 要进 17/6 之内的空档: r=21 即可（21^5 < 3^14 且 6·14=84 < 85=17·5）;
       r=22 也行（逐 q 整数扫描, 首个 q=27: 22^27 < 3^76 且 6·76=456 < 459=17·27）;
     - r=23: q ≤ 64 扫描无解（与 23^6 > 3^17 一致）
  8. 有界随机爬山（r=22, 种子/预算固定）: 只记录最优失配数 —— 有界尝试,
     不构成任何存在性/不存在性论断（rank ≤ 22 的真伪是公开问题, 此处不下判断）
  9. 发射: Agda 表子句 + 729 条 refl 骨架 + 证书数值 → /tmp/r23fetch/emitted_laderman.agda;
     TriRV C 数据表 → /tmp/r23fetch/trirv_data.c（由会话粘贴进 engineering/trirv/ 的 C 文件）

运行: python3 engineering/oracle_rank3_witness_gf3.py   （退出码 0 = 全部判据通过）
"""
import json
import random
import sys

# ---------------------------------------------------------------------------
# 证书原值（RakTikoo/matmul-333-tensor-rank certificates/*.json, 逐字转录;
# 每行 9 个位置之一, 每行 23 个系数, u_k(x) = U[x][k]）
# ---------------------------------------------------------------------------
LAD = {
    "U": [[0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 1, 1, 0, 0, 0, 1],
          [0, 0, 0, 0, 1, 0, 0, -1, 0, 1, 0, 1, 0, 0, 1, 0, 1, -1, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, -1, -1, 0, 0, 0, 0, 1, 0, 0],
          [1, 1, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
          [-1, 0, 0, -1, 1, 0, 1, 0, 0, 0, 0, 0, -1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, -1, 0, 0, 0, 1, 0, -1, -1, 0, 1, -1, -1, 0, 0, 0, 0, 0, 0, 0],
          [0, 1, 0, 0, -1, 1, -1, 0, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0],
          [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
    "V": [[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0],
          [0, 0, 0, 0, 0, 0, 0, 1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
          [0, 0, 0, -1, 0, 0, 0, -1, 0, 1, 1, -1, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0],
          [1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
          [-1, 0, 0, -1, 0, 1, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0],
          [0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 0],
          [0, 1, 0, 1, 1, 0, 1, 0, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 1, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    "W": [[0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0],
          [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
          [0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0],
          [1, 1, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
          [0, 1, 0, 1, 0, -1, 1, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, -1, 0, 1, -1, -1, -1, 0, 0, 0, 0, 0],
          [-1, 0, 0, 0, 1, 1, -1, -1, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
}

PER = {
    "U": [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
          [0, 0, 0, 0, 1, 0, 0, 0, -1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0],
          [0, 1, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 1, 0, -1],
          [0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 1, 0, 1, -1],
          [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0],
          [1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1],
          [1, 0, 0, 0, 1, -1, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]],
    "V": [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, -1, 0, 1],
          [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, -1, 0, -1, 0, 1, 0, -1, 0, 0, 0, 1, 0, -1],
          [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0],
          [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, -1],
          [1, -1, 0, -1, -1, 1, 0, -1, 1, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 1],
          [0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0, 1],
          [0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, -1, 0, 0, 1, -1, 0, 0, 0, 1, 1, -1],
          [1, -1, 0, -1, -1, 0, 0, -1, 0, -1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, -1, -1, 1],
          [1, 0, 0, -1, -1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
    "W": [[-1, -1, -1, 0, -1, 0, 0, -1, 0, 1, 0, -1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1],
          [-1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0],
          [1, 1, 1, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, -1, 0, 0, 0, 0, 0, -1],
          [1, 0, 0, 0, 1, 0, 0, 1, 0, -1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0],
          [0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, -1],
          [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1],
          [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
          [0, 0, 1, 1, -1, 0, 0, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]],
}

R = 23          # 项数
N = 9           # 每个指标的位置数（3×3）
TRIT = {-1: "T₂", 0: "T₀", 1: "T₁"}


# ---------------------------------------------------------------------------
# 基础件
# ---------------------------------------------------------------------------
def mm_tab():
    """⟨3,3,3⟩ 结构常数（729 项, 0/1）——与 Agda `mm 3` 逐字同构"""
    t = []
    for x in range(N):
        xr, xc = divmod(x, 3)
        for y in range(N):
            yr, yc = divmod(y, 3)
            for z in range(N):
                zr, zc = divmod(z, 3)
                t.append(1 if (xr == zr and xc == yr and yc == zc) else 0)
    return t


def contrib(U, V, W, k):
    """第 k 门的秩一贡献 u_k⊗v_k⊗w_k, 摊平成 729 维 GF(3) 向量"""
    out = []
    for x in range(N):
        for y in range(N):
            for z in range(N):
                out.append((U[x][k] * V[y][k] * W[z][k]) % 3)
    return out


def check_scheme(U, V, W, ring, mm=None):
    """逐点核对 Σ_k u_k(x)v_k(y)w_k(z) = mm(x,y,z)（ring 取模 3 或恒等=ℤ）。
    返回 (bad, hits, fires, dead_products)——bad=失配数, hits=非零目标命中数,
    fires=非零目标个数, dead_products=u/v/w 全零的门数（应为 0）"""
    if mm is None:
        mm = mm_tab()
    bad = hits = fires = 0
    idx = 0
    for x in range(N):
        for y in range(N):
            for z in range(N):
                s = ring(sum(U[x][k] * V[y][k] * W[z][k] for k in range(R)))
                t = mm[idx]
                fires += 1 if t else 0
                if s != ring(t):
                    bad += 1
                elif t:
                    hits += 1
                idx += 1
    dead = sum(1 for k in range(R)
               if all(U[x][k] == 0 for x in range(N))
               or all(V[y][k] == 0 for y in range(N))
               or all(W[z][k] == 0 for z in range(N)))
    return bad, hits, fires, dead


def gf3_rank(vectors):
    """GF(3) 上向量组的秩（Gauss 消元; 向量摊平成等长列表, 元素已归约到 0/1/2）"""
    rows = [list(v) for v in vectors]
    rank = 0
    cols = len(rows[0]) if rows else 0
    piv_col = 0
    while piv_col < cols and rank < len(rows):
        piv = None
        for i in range(rank, len(rows)):
            if rows[i][piv_col] % 3 != 0:
                piv = i
                break
        if piv is None:
            piv_col += 1
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = {1: 1, 2: 2}[rows[rank][piv_col] % 3]
        for i in range(rank + 1, len(rows)):
            f = (rows[i][piv_col] * inv) % 3
            if f:
                for c in range(piv_col, cols):
                    rows[i][c] = (rows[i][c] - f * rows[rank][c]) % 3
        rank += 1
        piv_col += 1
    return rank


def threshold_scan(r, qmax=64, base=3):
    """找最小的 q ≤ qmax 使 ∃p: r^q < base^p 且 6p < 17q（纯整数）。
    返回 (p, q) 或 None。p 取最小可行值。"""
    for q in range(1, qmax + 1):
        rq = r ** q
        p = 1
        while base ** p <= rq:
            p += 1
        if 6 * p < 17 * q:
            return (p, q)
    return None


# ---------------------------------------------------------------------------
# 判据
# ---------------------------------------------------------------------------
def check_structure():
    mm = mm_tab()
    fires = sum(mm)
    print(f"[1] 结构常数: 729 项中非零 {fires} 个（预期 27 = 3^3 个循环三元组）")
    assert fires == 27, fires
    # 非零位置恰是 (x=(i,j), y=(j,m), z=(i,m))
    for idx, v in enumerate(mm):
        x, rem = divmod(idx, 81)
        y, z = divmod(rem, 9)
        xr, xc = divmod(x, 3)
        yr, yc = divmod(y, 3)
        zr, zc = divmod(z, 3)
        expect = 1 if (zr == xr and yr == xc and zc == yc) else 0
        assert v == expect
    print(f"[1] 非零位置逐项核对 δ(xr,zr)δ(xc,yr)δ(yc,zc): {fires}/{fires} ✓")


def check_laderman_gf3():
    bad, hits, fires, dead = check_scheme(LAD["U"], LAD["V"], LAD["W"], lambda v: v % 3)
    print(f"[2] Laderman-23 GF(3): 729 点核对 bad={bad}, 非零命中 {hits}/{fires}, 空门 {dead}")
    assert bad == 0 and hits == 27 and fires == 27 and dead == 0
    nonz = sum(1 for k in range(R)
               if any(LAD["U"][x][k] for x in range(N))
               and any(LAD["V"][y][k] for y in range(N))
               and any(LAD["W"][z][k] for z in range(N)))
    print(f"[2] 每门 u,v,w 全非零: {nonz}/{R}")
    assert nonz == R


def check_laderman_Z():
    bad, hits, fires, dead = check_scheme(LAD["U"], LAD["V"], LAD["W"], lambda v: v)
    print(f"[3] Laderman-23 ℤ（整数恒等式）: bad={bad}, 非零命中 {hits}/{fires}")
    assert bad == 0 and hits == 27 and fires == 27
    vals = sorted({v for M in ("U", "V", "W") for row in LAD[M] for v in row})
    print(f"[3] 系数集 = {vals} ⊆ {{-1,0,1}} ⇒ 对任意交换环成立")
    assert vals == [-1, 0, 1]


def check_perminov_gf3():
    bad, hits, fires, dead = check_scheme(PER["U"], PER["V"], PER["W"], lambda v: v % 3)
    print(f"[4] Perminov-23 GF(3): bad={bad}, 非零命中 {hits}/{fires}, 空门 {dead}")
    assert bad == 0 and hits == 27 and fires == 27 and dead == 0


def check_negative_controls():
    def corrupt(M, pos, k):
        Uc = [list(r) for r in LAD["U"]]
        Vc = [list(r) for r in LAD["V"]]
        Wc = [list(r) for r in LAD["W"]]
        target = {"U": Uc, "V": Vc, "W": Wc}[M]
        target[pos][k] = (target[pos][k] + 1) % 3 if target[pos][k] != 1 else 2
        return Uc, Vc, Wc

    mm = mm_tab()
    Uc, Vc, Wc = corrupt("U", 0, 4)
    bad, *_ = check_scheme(Uc, Vc, Wc, lambda v: v % 3, mm)
    print(f"[5] 负控制 U[0][4]: bad={bad}（必须 > 0）")
    assert bad > 0
    Uc, Vc, Wc = corrupt("W", 8, 2)
    bad, *_ = check_scheme(Uc, Vc, Wc, lambda v: v % 3, mm)
    print(f"[5] 负控制 W[8][2]: bad={bad}（必须 > 0）")
    assert bad > 0
    mmc = list(mm)
    j = next(i for i, v in enumerate(mm) if v == 1)
    mmc[j] = 0
    bad, hits, fires, _ = check_scheme(LAD["U"], LAD["V"], LAD["W"], lambda v: v % 3, mmc)
    print(f"[5] 负控制 结构常数[{j}]: bad={bad}（必须 > 0）")
    assert bad > 0
    # 控制有效率: 23 门 × 9 位置逐一腐化, 全部必须转红
    red = 0
    for k in range(R):
        for pos in range(N):
            Uc, Vc, Wc = corrupt("U", pos, k)
            b, *_ = check_scheme(Uc, Vc, Wc, lambda v: v % 3, mm)
            red += 1 if b > 0 else 0
    print(f"[5] 全腐化扫描（U 侧 23×9）: 转红 {red}/207")
    assert red == 207


def check_independence():
    vecs = [contrib(LAD["U"], LAD["V"], LAD["W"], k) for k in range(R)]
    nnz = sum(1 for v in vecs if any(v))
    r23 = gf3_rank(vecs)
    print(f"[6] 23 个秩一贡献: 非零 {nnz}/{R}, GF(3) 秩 = {r23}")
    assert nnz == R and r23 == R
    # 控制向量组: 只取前 22 门 ⇒ 秩必须 < 23
    r22 = gf3_rank(vecs[:22])
    print(f"[6] 控制组（前 22 门）: 秩 = {r22} < 23 ✓")
    assert r22 == 22
    print("[6] ⇒ 丢弃任何一门都不再是分解（删除封闭; 有界否定数据点）")


def check_thresholds():
    p7, t20 = 23 ** 7, 3 ** 20
    print(f"[7] 23^7 = {p7} < 3^20 = {t20}: {p7 < t20}")
    assert p7 < t20
    p6, t17 = 23 ** 6, 3 ** 17
    print(f"[7] 23^6 = {p6} > 3^17 = {t17}: {p6 > t17}")
    assert p6 > t17
    # r=21 / r=22 进入空档的首个 (p,q); r=23 无解
    for r, want in ((21, True), (22, True), (23, False)):
        hit = threshold_scan(r, qmax=64)
        print(f"[7] n=3, r={r}: q≤64 内进入 17/6 之下的 (p,q) = {hit}")
        if want:
            assert hit is not None
            p, q = hit
            assert (r ** q) < (3 ** p) and 6 * p < 17 * q
        else:
            assert hit is None
    print("[7] 阈值含义: n=3 上 r=21/22 都能进 17/6 之内的空档（31/11 ≈ 2.818）,"
          " r=23 不能 —— 与 23^6 > 3^17 的无界论证一致")


# ---------------------------------------------------------------------------
# 有界随机爬山（r=22; 只是有界尝试, 不下存在性/不存在性结论）
# ---------------------------------------------------------------------------
def bounded_search(seed=20261126, restarts=6, steps=12000):
    rng = random.Random(seed)
    mm = mm_tab()
    best_overall = 729

    def score(res):
        return sum(1 for v in res if v % 3 != 0)

    for restart in range(restarts):
        # 随机 22 门起点
        U = [[rng.choice((-1, 0, 0, 1)) for _ in range(22)] for _ in range(N)]
        V = [[rng.choice((-1, 0, 0, 1)) for _ in range(22)] for _ in range(N)]
        W = [[rng.choice((-1, 0, 0, 1)) for _ in range(22)] for _ in range(N)]
        # 残差 R = mm − Σ 贡献（GF(3)）
        res = []
        idx = 0
        for x in range(N):
            for y in range(N):
                for z in range(N):
                    s = sum(U[x][k] * V[y][k] * W[z][k] for k in range(22)) % 3
                    res.append((mm[idx] - s) % 3)
                    idx += 1
        cur = score(res)
        best = cur
        for step in range(steps):
            k = rng.randrange(22)
            which = rng.randrange(3)
            x0 = rng.randrange(N)
            newv = rng.choice((-1, 0, 1))
            src = (U, V, W)[which]
            old = src[x0][k]
            if old == newv:
                continue
            src[x0][k] = newv
            # 增量更新残差: 只动 (x0, ·, ·)（U 侧）/（·, x0, ·）（V 侧）/（·, ·, x0）（W 侧）
            affected = []
            if which == 0:
                for y in range(N):
                    for z in range(N):
                        affected.append((x0 * 81 + y * 9 + z, V[y][k] * W[z][k]))
            elif which == 1:
                for x in range(N):
                    for z in range(N):
                        affected.append((x * 81 + x0 * 9 + z, U[x][k] * W[z][k]))
            else:
                for x in range(N):
                    for y in range(N):
                        affected.append((x * 81 + y * 9 + x0, U[x][k] * V[y][k]))
            delta = (newv - old) % 3
            before = sum(1 for i, _ in affected if res[i] != 0)
            for i, coef in affected:
                res[i] = (res[i] - delta * coef) % 3
            after = sum(1 for i, _ in affected if res[i] != 0)
            cand = cur + (after - before)
            if cand <= cur:
                cur = cand
                if cand < best:
                    best = cand
            else:
                # 回滚
                src[x0][k] = old
                for i, coef in affected:
                    res[i] = (res[i] + delta * coef) % 3
        best_overall = min(best_overall, best)
        print(f"[8] 爬山 restart {restart}: 最优失配 {best}/729")
    print(f"[8] 有界爬山总最优: {best_overall}/729（种子 {seed}, restarts {restarts}, steps {steps}）")
    print("[8] 注: 这只是预算固定的有界尝试; r ≤ 22 的存在性问题不由此判定")
    return best_overall


# ---------------------------------------------------------------------------
# 发射
# ---------------------------------------------------------------------------
def fin3(i):
    return ["fzero", "fsuc fzero", "fsuc (fsuc fzero)"][i]


def fin23(k):
    s = "fzero"
    for _ in range(k):
        s = "fsuc (" + s + ")"
    return s


def emit_agda(path="/tmp/r23fetch/emitted_laderman.agda"):
    lines = []
    lines.append("-- ↓↓ 本段由 engineering/oracle_rank3_witness_gf3.py 发射（先算后验）, 请勿手改 ↓↓")
    for name, M, dom in (("raL", LAD["U"], "Pos 3"), ("rbL", LAD["V"], "Pos 3"),
                         ("rcL", LAD["W"], "Out 3")):
        lines.append(f"{name} : Fin 23 → {dom} → Trit")
        for k in range(R):
            for pos in range(N):
                i, j = divmod(pos, 3)
                lines.append(f"{name} ({fin23(k)}) ({fin3(i)} , {fin3(j)}) = {TRIT[M[pos][k]]}")
    lines.append("")
    lines.append("rank-eqL : ∀ (x y : Pos 3) (z : Out 3) →")
    lines.append("  sumFin (λ i → (raL i x) ⊗ ((rbL i y) ⊗ (rcL i z))) ≡ mm 3 x y z")
    for xi in range(3):
        for xj in range(3):
            for yi in range(3):
                for yj in range(3):
                    branches = " ; ".join(
                        f"({fin3(zi)} , {fin3(zj)}) → refl"
                        for zi in range(3) for zj in range(3))
                    lines.append(
                        f"rank-eqL ({fin3(xi)} , {fin3(xj)}) ({fin3(yi)} , {fin3(yj)})"
                        f" = λ {{ {branches} }}")
    lines.append("-- ↑↑ 发射段结束 ↑↑")
    text = "\n".join(lines) + "\n"
    with open(path, "w") as f:
        f.write(text)
    import re
    n_tab = sum(1 for ln in lines if re.match(r"^(raL|rbL|rcL) \((fzero|fsuc)", ln))
    n_eq = sum(1 for ln in lines if ln.startswith("rank-eqL ("))
    print(f"[9] Agda 发射 → {path}: 表子句 {n_tab}（预期 {3 * R * N}）, rank-eq 子句 {n_eq}（预期 81）")
    assert n_tab == 3 * R * N and n_eq == 81
    assert "?" not in text and "{!" not in text
    # 证书数值（供 Agda 侧核对, 不手算）
    vals = {
        "p7": 23 ** 7, "t20": 3 ** 20, "d20": 3 ** 20 - 23 ** 7 - 1,
        "t17": 3 ** 17, "p6": 23 ** 6, "d6": 23 ** 6 - 3 ** 17,
    }
    print(f"[9] 证书数值: 3^17 = {vals['t17']}, 23^6 = {vals['p6']}, "
          f"差 = {vals['d6']}; 23^7 = {vals['p7']}, 3^20 = {vals['t20']}, "
          f"3^20 − 23^7 − 1 = {vals['d20']}")
    return text


def emit_trirv(path="/tmp/r23fetch/trirv_data.c"):
    def flat(M):
        return ", ".join(str(M[pos][k]) for pos in range(N) for k in range(R))
    text = (
        "/* Laderman-23 系数表（行主序: u[pos*23+k] = U[pos][k], pos = 3*行+列）\n"
        " * 由 engineering/oracle_rank3_witness_gf3.py 发射, 请勿手改 */\n"
        f"int lad_U[621] = {{ {flat(LAD['U'])} }};\n"
        f"int lad_V[621] = {{ {flat(LAD['V'])} }};\n"
        f"int lad_W[621] = {{ {flat(LAD['W'])} }};\n"
    )
    with open(path, "w") as f:
        f.write(text)
    print(f"[9] TriRV 数据 → {path}: 3×621 系数")
    return text


# ---------------------------------------------------------------------------
def main():
    check_structure()
    check_laderman_gf3()
    check_laderman_Z()
    check_perminov_gf3()
    check_negative_controls()
    check_independence()
    check_thresholds()
    bounded_search()
    emit_agda()
    emit_trirv()
    print("ALL_PASS")


if __name__ == "__main__":
    sys.exit(0 if main() is None else 1)
