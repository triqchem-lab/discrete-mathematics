#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_capacity_probe.py —— F₃ 上 ⟨3,3,3⟩ 的「容量–剖面」探针（零外部依赖）

背景（PROVEN §二十三）: 「互补幂等」法（Yang 等, arXiv:2609.18722）只有在 Σ_t rank(a_t) = n³（Δ = 0）时
才有刚性可用。要在 F₃ 上走这条路, 先得知道 r = 19 的容量约束是否把每个假想分解都逼进 Δ = 0。
本件是那台探针的 Python 一侧:

  · 容量表（纯 Python, 只读证书）: 若 ⟨3,3,3⟩ 有 r 项分解, 首因子 a_t ∈ A（9 维）, 对每个子空间 W ⊆ A
        N(W) + L(W^⊥) ≤ r,   N(W) = #{t : a_t ∈ W},
    因为把第一变元限制到 V ⊆ W^⊥ 会消掉首因子落在 W 里的项, 剩下 r − N(W) 项给出 T|_{V×B×C} 的分解。
    证书 engineering/wang_f3ext/certs/matrix_q03_n333_v1.pb.txt 的 736 个轨道给出所有 W^⊥ 的下界 L
    （「余维 c」的条目 = dim W = c）。
  · 查表件（C++, 需单独构建; 缺失时跳过）: engineering/wang_f3ext/standalone/orbit_lookup.cc,
    装入全部 736 个轨道后可对任意子空间 W 一次查到 L(W^⊥), 并完备地检查一个首因子配置。
    这里用**独立写的** Python 线性代数与群作用实现给它做五道验证:
      1. 自检（随机群像必命中并还原）;
      2. 见证重放 v ↦ (L·τᵗ(v))·R⁻¹ 必落回证书条目的子空间;
      3. 与纯 Python 的子集枚举互证（候选数与违规多重集逐项相同）;
      4. Laderman 的真实 23 项分解的首因子在 r = 23 下零违规（真实分解必然满足容量约束）;
      5. L = 12 的那个平面轨道的精确结构（穷举过三条固定直线的全部平面 + 双计数）:
         平面里 8 个非零元素全部可逆, 即 K = A·span{I, N}, N 没有 F₃ 特征值; 这类平面共 808,704 个 = 10.02%。

用法:
  python3 engineering/wang_capacity_probe.py [--lookup <orbit_lookup 二进制>]
  缺省找 $ORBIT_LOOKUP 或 /tmp/wang-f3/orbit_lookup; 构建见 build.sh 的 lookup 目标。
诚实边界: 证书界是下界, 不是受限制张量的真实秩; 「零违规」只针对按证书界写出的约束。
"""
import argparse
import itertools
import os
import random
import subprocess
import sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
if HERE not in sys.path:
    sys.path.insert(0, HERE)
import wang_cert_check as base          # noqa: E402
import wang_cert_check_fq as W          # noqa: E402

CERT = os.path.join(HERE, "wang_f3ext", "certs", "matrix_q03_n333_v1.pb.txt")
N = 9
EXPECTED_HIST = {
    0: {17: 1}, 1: {16: 3}, 2: {15: 14},
    3: {13: 1, 14: 80, 15: 3},
    4: {12: 3, 13: 112, 14: 151},
    5: {10: 1, 11: 4, 12: 95, 13: 166},
    6: {9: 6, 10: 8, 11: 30, 12: 36, 13: 4},
    7: {6: 2, 8: 1, 9: 6, 10: 2, 11: 2, 12: 1},
    8: {3: 1, 6: 1, 9: 1}, 9: {0: 1},
}


# ---------- 证书 → 轨道 → 容量表（纯 Python） ----------
def load_orbits(path=CERT):
    """每个轨道: dict(codim = 约束行数 = dim W, bound, kind, index, rows = 约束行)"""
    cert = base.parse_certificate(path)
    assert cert["characteristic"] == 3, cert["characteristic"]
    assert cert["na"] == N, cert["na"]
    out = []
    for o in cert["orbits"]:
        rows = W.rows_from_bytes_fq(b"".join(o["raw_rows"]), N)
        out.append(dict(codim=len(rows), bound=o["rank_lower_bound"] or 0, kind=o["kind"],
                        index=o["index"], rows=[[W.digit(v, k) for k in range(N)] for v in rows]))
    assert len(out) == 736, len(out)
    return out


def capacity_table(orbits, r):
    """{dim W: dict(hist = {L: 轨道数}, capmin, capmax, n)}; cap = r − L(W^⊥)"""
    tab = {}
    for d in range(10):
        bs = [o["bound"] for o in orbits if o["codim"] == d]
        assert bs, d
        tab[d] = dict(hist=dict(sorted(Counter(bs).items())), capmin=r - max(bs), capmax=r - min(bs), n=len(bs))
    return tab


def delta_profiles(r):
    """Δ = Σ rank − 27 按秩剖面 (n₁, n₂, n₃) 分组"""
    by = defaultdict(list)
    for n1 in range(r + 1):
        for n2 in range(r + 1 - n1):
            n3 = r - n1 - n2
            by[n1 + 2 * n2 + 3 * n3 - 27].append((n1, n2, n3))
    return {k: sorted(v) for k, v in by.items()}


# ---------- F₃ 线性代数（纯 Python, 独立于框架） ----------
def rref(rows):
    """最左主元 RREF: 返回 (基, 秩)"""
    m = [list(x) for x in rows if any(v % 3 for v in x)]
    r0 = 0
    for c in range(len(m[0])) if m else ():
        p = next((i for i in range(r0, len(m)) if m[i][c] % 3), None)
        if p is None:
            continue
        m[r0], m[p] = m[p], m[r0]
        iv = 1 if m[r0][c] == 1 else 2
        m[r0] = [(x * iv) % 3 for x in m[r0]]
        for i in range(len(m)):
            if i != r0 and m[i][c] % 3:
                f = m[i][c]
                m[i] = [(x - f * y) % 3 for x, y in zip(m[i], m[r0])]
        r0 += 1
    return [tuple(m[i]) for i in range(r0)], r0


def in_span(p, basis):
    v = list(p)
    for b in basis:
        c = next(i for i, x in enumerate(b) if x)
        if v[c] % 3:
            f = v[c]
            v = [(x - f * y) % 3 for x, y in zip(v, b)]
    return not any(x % 3 for x in v)


def rank3(v):
    return rref([[v[3 * i + j] for j in range(3)] for i in range(3)])[1]


def mat_mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(3)) % 3 for j in range(3)] for i in range(3)]


def mat_inv(a):
    m = [list(row) + [1 if i == j else 0 for j in range(3)] for i, row in enumerate(a)]
    for c in range(3):
        p = next(i for i in range(c, 3) if m[i][c] % 3)
        m[c], m[p] = m[p], m[c]
        iv = 1 if m[c][c] == 1 else 2
        m[c] = [(x * iv) % 3 for x in m[c]]
        for i in range(3):
            if i != c and m[i][c] % 3:
                f = m[i][c]
                m[i] = [(x - f * y) % 3 for x, y in zip(m[i], m[c])]
    return [row[3:] for row in m]


def data_to_mat(d):
    """FqMatrix 的数据: 3^k 位上的数位 = 矩阵元素（行主序, 低位在前）"""
    return [[(d // (3 ** (3 * i + j))) % 3 for j in range(3)] for i in range(3)]


# ---------- 查表件 ----------
class LookupTool:
    """orbit_lookup 的薄封装。分批往返（每批 200 条）: 一次写太多会填满工具的输出管道, 两边互等。"""

    def __init__(self, binary, cert=CERT):
        self.cert = cert
        self.p = subprocess.Popen([binary, cert], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                  stderr=subprocess.DEVNULL, text=True, bufsize=1)

    def close(self):
        if self.p.poll() is None:
            try:
                self.p.stdin.close()
            except OSError:
                pass
            self.p.wait(timeout=30)
        for pipe in (self.p.stdout, self.p.stderr):
            if pipe is not None:
                pipe.close()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.close()

    def selftest(self, seed=7, k=4):
        self.p.stdin.write("S %d %d\n" % (seed, k))
        self.p.stdin.flush()
        f = self.p.stdout.readline().split()
        assert f[0] == "SELFTEST", f
        return int(f[1]), int(f[2]), int(f[3])

    def ask(self, queries, chunk=200):
        """queries: 子空间的基的列表 → [(界, 证书位置, query_elem, store_elem)]"""
        out = [None] * len(queries)
        for s in range(0, len(queries), chunk):
            part = queries[s:s + chunk]
            for i, rows in enumerate(part):
                self.p.stdin.write("Q %d %d %s\n" % (i, len(rows), " ".join("".join(map(str, r)) for r in rows)))
            self.p.stdin.flush()
            for _ in range(len(part)):
                f = self.p.stdout.readline().split()
                assert f and f[0] == "R", f
                out[s + int(f[1])] = (int(f[2]), int(f[3]), int(f[4]), int(f[5]))
        return out

    def config(self, r, points):
        """C 命令: (候选数, 违规数, 超出之和), 逐维 {(候选, 违规)}, 违规 [(dim, N, L)]"""
        self.p.stdin.write("C %d %d %s\n" % (r, len(points), " ".join("".join(map(str, p)) for p in points)))
        self.p.stdin.flush()
        per_dim, viol = {}, []
        while True:
            line = self.p.stdout.readline()
            if not line:
                raise RuntimeError("orbit_lookup 意外退出")
            f = line.split()
            if f[0] == "D":
                per_dim[int(f[1])] = (int(f[2]), int(f[3]))
            elif f[0] == "V":
                viol.append((int(f[1]), int(f[2]), int(f[3])))
            elif f[0] == "Z":
                return (int(f[1]), int(f[2]), int(f[3])), per_dim, viol

    def witness_ok(self, rows, bound, pos, qe, se, orbits):
        """独立复核: v ↦ (L·τᵗ(v))·R⁻¹ 的张成 = 证书条目 pos 的子空间, 且界一致"""
        L = data_to_mat(qe & 0xFFFF)
        t = (qe >> 16) & 0xFFFF
        rinv = mat_inv(data_to_mat(se))
        back = []
        for v in rows:
            V = [[v[3 * i + j] for j in range(3)] for i in range(3)]
            if t:
                V = [list(x) for x in zip(*V)]
            X = mat_mul(mat_mul(L, V), rinv)
            back.append([X[i][j] for i in range(3) for j in range(3)])
        return rref(back)[0] == rref(orbits[pos]["rows"])[0] and bound == orbits[pos]["bound"]


def python_violations(points, tool, r, tab):
    """纯 Python 的子集枚举（完备, 与 C 的子集法是两套独立实现）: 返回违规多重集 {(dim, N, L): 个数}"""
    n = len(points)
    by_size = defaultdict(list)
    for d in range(1, 9):
        by_size[tab[d]["capmin"] + 1].append(d)
    cand = {}
    for size, ds in sorted(by_size.items()):
        for S in itertools.combinations(range(n), size):
            rows = [points[i] for i in S]
            b, rk = rref(rows)
            if rk in ds:
                cand.setdefault(tuple(b), rk)
    answers = tool.ask([list(k) for k in cand])
    out = Counter()
    for key, d, (bound, pos, qe, se) in zip(cand, cand.values(), answers):
        nw = sum(1 for p in points if in_span(p, key))
        if nw + bound > r:
            out[(d, nw, bound)] += 1
    return len(cand), out


def annihilator(basis):
    """{x : x 与 basis 的每个向量都正交} 的一组基（纯 Python 的零空间）"""
    M = [list(r) for r in basis]
    piv = []
    r0 = 0
    for c in range(N):
        p_ = next((i for i in range(r0, len(M)) if M[i][c] % 3), None)
        if p_ is None:
            continue
        M[r0], M[p_] = M[p_], M[r0]
        iv = 1 if M[r0][c] == 1 else 2
        M[r0] = [(x * iv) % 3 for x in M[r0]]
        for i in range(len(M)):
            if i != r0 and M[i][c] % 3:
                f = M[i][c]
                M[i] = [(x - f * y) % 3 for x, y in zip(M[i], M[r0])]
        piv.append(c)
        r0 += 1
    out = []
    for f in range(N):
        if f in piv:
            continue
        x = [0] * N
        x[f] = 1
        for i, p_ in enumerate(piv):
            x[p_] = (-M[i][f]) % 3
        out.append(x)
    return out


def planes_through(anchor):
    """过直线 ⟨anchor⟩ 的全部平面, 每个给它的零化子（7 行, 即查表件要的约束行）; 共 (3⁸ − 1)/2 = 3280 个。
    平面 ↔ 8 维商空间里的直线: 取「anchor 的首个非零坐标处为 0、首个非零分量为 1」的向量作代表。"""
    k0 = next(i for i, x in enumerate(anchor) if x)
    out = []
    for code in range(3 ** (N - 1)):
        v = [0] * N
        c = code
        for i in range(N):
            if i == k0:
                continue
            v[i] = c % 3
            c //= 3
        if not any(v):
            continue
        first = next(i for i, x in enumerate(v) if x)
        if v[first] != 1:
            continue
        out.append(annihilator([list(anchor), v]))
    assert len(out) == 3280, len(out)
    return out


def det3(a):
    return (a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
            - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
            + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])) % 3


def no_eigenvalue_count():
    """没有 F₃ 特征值的 3×3 矩阵个数（全枚举 3⁹ = 19683 个; 每个这样的 N 生成 M₃ 里的一份 F₂₇）"""
    cnt = 0
    for d in itertools.product(range(3), repeat=9):
        if all(det3([[d[3 * i + j] - (x if i == j else 0) for j in range(3)] for i in range(3)]) for x in range(3)):
            cnt += 1
    return cnt


def pencil_facts(A, B):
    """束 span{A, B}（两个 9 维向量）: (8 个非零元素是否全部可逆, det(xA + yB) 的系数 {(a, b): c})"""
    allinv = all(det3([[(x * A[3 * i + j] + y * B[3 * i + j]) % 3 for j in range(3)] for i in range(3)])
                 for x in range(3) for y in range(3) if (x, y) != (0, 0))

    def f(x, y):
        return det3([[(x * A[3 * i + j] + y * B[3 * i + j]) % 3 for j in range(3)] for i in range(3)])

    c30, c03 = f(1, 0), f(0, 1)
    c21 = (f(1, 2) - f(1, 1) - c03) % 3
    c12 = (f(1, 1) - c30 - c21 - c03) % 3
    coef = {(3, 0): c30, (2, 1): c21, (1, 2): c12, (0, 3): c03}
    # 插值结果要对全部 (x, y) 复核
    for x in range(3):
        for y in range(3):
            assert sum(c * pow(x, a, 3) * pow(y, b, 3) for (a, b), c in coef.items()) % 3 == f(x, y)
    return allinv, coef


GL3 = (27 - 1) * (27 - 3) * (27 - 9)          # |GL₃(F₃)| = 11232
PLANES = (3 ** 9 - 1) * (3 ** 8 - 1) // ((3 ** 2 - 1) * (3 - 1))   # [9 choose 2]₃ = 8,069,620


def plane_structure(tool, orbits):
    """L = 12 的那个平面轨道的精确结构（穷举 + 双计数）。返回 dict, 各项的含义见 run 里的断言。"""
    res = {}
    for name, anc in (("E11", (1, 0, 0, 0, 0, 0, 0, 0, 0)),
                      ("E11+E22", (1, 0, 0, 0, 1, 0, 0, 0, 0)),
                      ("I", (1, 0, 0, 0, 1, 0, 0, 0, 1))):
        ans = tool.ask(planes_through(anc), chunk=250)
        res[name] = Counter(b for b, p_, qe, se in ans)
    bad = [o for o in orbits if o["codim"] == 7 and o["bound"] == 12]
    res["n_bad_orbits"] = len(bad)
    basis = annihilator(bad[0]["rows"])        # 约束行张成 7 维 W, 零化子就是那个平面
    res["plane_dim"] = len(basis)
    res["allinv"], res["coef"] = pencil_facts(basis[0], basis[1])
    res["n_noeig"] = no_eigenvalue_count()
    res["planes_a"] = GL3 * res["n_noeig"] // 48       # 每个平面 48 组有序基
    res["planes_b"] = res["I"][12] * GL3 // 8           # 每个平面 8 个可逆元素
    res["frac"] = res["planes_a"] / PLANES
    return res


def random_point(rng):
    while True:
        v = tuple(rng.randrange(3) for _ in range(N))
        if any(v):
            return v


def random_config(rng, k=19):
    pts, seen = [], set()
    while len(pts) < k:
        v = random_point(rng)
        if v not in seen:
            seen.add(v)
            pts.append(v)
    return pts


def random_subspace(rng, d):
    while True:
        b, rk = rref([list(random_point(rng)) for _ in range(d)])
        if rk == d:
            return [list(x) for x in b]


def laderman_first_factors():
    import oracle_rank3_witness_gf3 as O
    k = len(O.LAD["U"][0])
    return [tuple(O.LAD["U"][x][i] % 3 for x in range(N)) for i in range(k)]


def default_binary():
    return os.environ.get("ORBIT_LOOKUP", "/tmp/wang-f3/orbit_lookup")


def run(binary=None, seed=20261128):
    orbits = load_orbits()
    hist = {d: Counter(o["bound"] for o in orbits if o["codim"] == d) for d in range(10)}
    assert hist == EXPECTED_HIST, {d: dict(hist[d]) for d in range(10)}
    r = 19
    tab = capacity_table(orbits, r)
    print("证书 736 个轨道的界分布与记录一致; r = %d 的容量表:" % r)
    for d in range(1, 9):
        t = tab[d]
        print("  dim W = %d: L ∈ %s → cap ∈ %d..%d" % (d, sorted(t["hist"]), t["capmin"], t["capmax"]))
    prof = delta_profiles(r)
    print("  Δ = 0 的秩剖面: %s; Δ = 1: %s" % (prof[0], prof[1]))
    binary = binary or default_binary()
    if not os.path.exists(binary):
        print("查表件 %s 不存在 —— 跳过查表验证（构建: bash engineering/wang_f3ext/build.sh 3 lookup %s）" % (binary, binary))
        print("wang_capacity_probe: TABLE_ONLY")
        return "TABLE_ONLY"
    rng = random.Random(seed)
    tool = LookupTool(binary)
    try:
        n, images, fails = tool.selftest(seed, 4)
        assert n == 736 and images == 736 * 4 and fails == 0, (n, images, fails)
        print("验证 1 自检: %d 条目 × 4 个随机群像, 失败 %d" % (n, fails))
        qs = [random_subspace(rng, 7) for _ in range(30)] + [random_subspace(rng, 3) for _ in range(30)]
        ans = tool.ask(qs)
        ok = sum(tool.witness_ok(q, b, p, qe, se, orbits) for q, (b, p, qe, se) in zip(qs, ans))
        assert ok == len(qs), (ok, len(qs))
        print("验证 2 见证重放（Python 自己的群作用实现）: %d/%d" % (ok, len(qs)))
        pts = random_config(rng)
        z, per_dim, viol = tool.config(r, pts)
        ncand, pyviol = python_violations(pts, tool, r, tab)
        cviol = Counter(viol)
        assert ncand == z[0] and pyviol == cviol, (ncand, z, sorted(pyviol.items())[:3], sorted(cviol.items())[:3])
        assert z[1] > 0, "随机配置应当有违规（否则这道互证是空转）"
        print("验证 3 两套完备枚举互证: 候选 %d / 违规 %d, 多重集逐项相同" % (z[0], z[1]))
        lad = laderman_first_factors()
        assert len(lad) == 23
        z23, _, v23 = tool.config(23, lad)
        assert z23[0] > 0 and z23[1] == 0, z23
        z22, _, _ = tool.config(22, lad)
        assert z22[1] > 0, "r = 22 应当出现违规（否则验证 4 的对照是空转）"
        sr = sum(rank3(p) for p in lad)
        print("验证 4 Laderman 23 个真实首因子（Σ 秩 = %d）: r = 23 候选 %d / 违规 %d; 对照 r = 22 违规 %d"
              % (sr, z23[0], z23[1], z22[1]))
        # 验证 5: L = 12 的那个平面轨道的精确结构（穷举 + 双计数）
        ps = plane_structure(tool, orbits)
        assert ps["n_bad_orbits"] == 1 and ps["plane_dim"] == 2
        assert sorted(ps["E11"]) == [6, 9, 10] and [ps["E11"][b] for b in (6, 9, 10)] == [152, 2552, 576]
        assert sorted(ps["E11+E22"]) == [6, 8, 9, 10, 11], dict(ps["E11+E22"])
        assert [ps["E11+E22"][b] for b in (6, 8, 9, 10, 11)] == [6, 3, 1345, 1296, 630]
        assert sorted(ps["I"]) == [9, 10, 11, 12] and ps["I"][12] == 576
        assert ps["allinv"] and ps["coef"] == {(3, 0): 1, (2, 1): 1, (1, 2): 2, (0, 3): 1}
        assert ps["n_noeig"] == 3456 and ps["planes_a"] == ps["planes_b"] == 808704
        print("验证 5 L = 12 平面的结构: 过 E₁₁ 的 3280 个平面 L 只取 6/9/10 (152/2552/576); 过 E₁₁+E₂₂ 的从不取 12; "
              "过 I 的有 576 个; 该轨道的代表束 8 个非零元素全可逆, det(xA+yB) = x³+x²y+2xy²+y³; "
              "无 F₃ 特征值的 3×3 矩阵 %d 个 ⟹ 这类平面 %d 个 (%.2f%%), 两种数法一致"
              % (ps["n_noeig"], ps["planes_a"], 100 * ps["frac"]))
    finally:
        tool.close()
    print("wang_capacity_probe: ALL_PASS")
    return "ALL_PASS"


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description="F₃ ⟨3,3,3⟩ 的容量–剖面探针")
    ap.add_argument("--lookup", default=None, help="orbit_lookup 二进制（缺省 $ORBIT_LOOKUP 或 /tmp/wang-f3/orbit_lookup）")
    ap.add_argument("--seed", type=int, default=20261128)
    a = ap.parse_args()
    sys.exit(0 if run(a.lookup, a.seed) in ("ALL_PASS", "TABLE_ONLY") else 1)
