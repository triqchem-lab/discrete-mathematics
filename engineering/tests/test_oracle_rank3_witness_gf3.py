#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""oracle_rank3_witness_gf3 的回归测试（unittest, 零外部依赖）

对应:
  · oracle : engineering/oracle_rank3_witness_gf3.py
  · Agda   : src/Sovereign/Algebra/LinearAlgebra/TensorRankLadermanGF3.agda   (M17)
             ★ rank-laderman : RankLE₃ 3 23（Laderman 1976 的 23 门, 729 条 refl）
             ★ laderman-saving : ∀ p q → 0 < q → 20*q ≤ 7*p → Saving₃ p q
             ★ laderman-not-below : 6*p < 17*q → 23^q < 3^p → ⊥（(3,23) 不越过 17/6）
  · TriRV  : engineering/trirv/laderman23_gf3.c（三进制 VM 独立核验, 返回 0 = 全对）
  · 证书   : GitHub RakTikoo/matmul-333-tensor-rank（系数 ∈ {-1,0,1}, ℤ 恒等式）

本测试不重证任何定理（裁决在 Agda 内核 + VM）; 它守住:
  1. oracle 判据全部通过且**非空转**（27 个结构常数 / 23 门 / 207 次腐化全转红）;
  2. 负控制有区分力（改一个系数 / 改一个结构常数必须转红）;
  3. Agda 件在盘上、主签名原样、零 postulate / 0 REWRITE / 零洞、子句数 621+81;
  4. Agda 表子句与 oracle 表**逐字一致**（发射不失真）;
  5. TriRV C 件: 无位运算惯用法（C-TERNARY-PITFALLS 铁律）、PK 打包表解包后与 oracle 表一致。
"""

import importlib.util
import os
import re
import sys
import unittest
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ORACLE = os.path.join(ROOT, "engineering", "oracle_rank3_witness_gf3.py")
AGDA = os.path.join(ROOT, "src", "Sovereign", "Algebra", "LinearAlgebra",
                    "TensorRankLadermanGF3.agda")
TRIRV = os.path.join(ROOT, "engineering", "trirv", "laderman23_gf3.c")


def load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_rank3_witness_gf3", ORACLE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def run_quiet(fn):
    buf = io.StringIO()
    with redirect_stdout(buf):
        fn()
    return buf.getvalue()


import io  # noqa: E402  (放这里保持导入集中)


class OracleRank3WitnessGF3(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.mod = load_oracle()

    # ---- 1. 判据通过 + 非空转 ------------------------------------------------

    def test_structure_constants(self):
        run_quiet(self.mod.check_structure)          # 内含 fires == 27 断言
        mm = self.mod.mm_tab()
        self.assertEqual(len(mm), 729)
        self.assertEqual(sum(mm), 27)

    def test_laderman_gf3(self):
        bad, hits, fires, dead = self.mod.check_scheme(
            self.mod.LAD["U"], self.mod.LAD["V"], self.mod.LAD["W"], lambda v: v % 3)
        self.assertEqual((bad, hits, fires, dead), (0, 27, 27, 0))

    def test_laderman_Z_exact(self):
        bad, hits, fires, dead = self.mod.check_scheme(
            self.mod.LAD["U"], self.mod.LAD["V"], self.mod.LAD["W"], lambda v: v)
        self.assertEqual((bad, hits, fires, dead), (0, 27, 27, 0))
        vals = sorted({v for M in "UVW" for row in self.mod.LAD[M] for v in row})
        self.assertEqual(vals, [-1, 0, 1])

    def test_perminov_gf3(self):
        bad, hits, fires, dead = self.mod.check_scheme(
            self.mod.PER["U"], self.mod.PER["V"], self.mod.PER["W"], lambda v: v % 3)
        self.assertEqual((bad, hits, fires, dead), (0, 27, 27, 0))

    def test_contribution_independence(self):
        vecs = [self.mod.contrib(self.mod.LAD["U"], self.mod.LAD["V"],
                                 self.mod.LAD["W"], k) for k in range(23)]
        self.assertEqual(self.mod.gf3_rank(vecs), 23)     # 删除封闭
        self.assertEqual(self.mod.gf3_rank(vecs[:22]), 22)  # 控制组

    def test_thresholds(self):
        self.assertLess(23 ** 7, 3 ** 20)
        self.assertGreater(23 ** 6, 3 ** 17)
        self.assertEqual(self.mod.threshold_scan(21, qmax=64), (14, 5))
        self.assertEqual(self.mod.threshold_scan(22, qmax=64), (31, 11))
        self.assertIsNone(self.mod.threshold_scan(23, qmax=64))

    def test_bounded_search_smoke(self):
        best = self.mod.bounded_search(seed=20261126, restarts=1, steps=200)
        self.assertIsInstance(best, int)
        self.assertTrue(0 <= best <= 729)

    # ---- 2. 负控制（判据有区分力） -------------------------------------------

    def test_negative_controls(self):
        run_quiet(self.mod.check_negative_controls)  # 内含 207/207 转红断言

    def test_single_corruption_matrix(self):
        """U/V/W 三侧各抽 5 门逐一腐化, 全部必须转红（抽查版, 全量 207 在 oracle 主程序）"""
        mod = self.mod
        mm = mod.mm_tab()
        checked = 0
        for side, M in (("U", mod.LAD["U"]), ("V", mod.LAD["V"]), ("W", mod.LAD["W"])):
            for k in range(0, 23, 5):
                for pos in (0, 4, 8):
                    C = {s: [list(r) for r in mod.LAD[s]] for s in "UVW"}
                    C[side][pos][k] = (C[side][pos][k] + 1) % 3 if C[side][pos][k] != 1 else 2
                    bad, *_ = mod.check_scheme(C["U"], C["V"], C["W"],
                                               lambda v: v % 3, mm)
                    self.assertGreater(bad, 0, (side, pos, k))
                    checked += 1
        self.assertEqual(checked, 45)                 # 前提火计: 抽查非空转

    # ---- 3. Agda 件 ----------------------------------------------------------

    def test_agda_file_discipline(self):
        text = read(AGDA)
        self.assertTrue(os.path.exists(AGDA))
        body = "\n".join(line.split("--")[0] for line in text.split("\n"))
        self.assertNotIn("postulate", body)
        self.assertNotIn("REWRITE", body)
        self.assertNotIn("{!", body)
        self.assertNotIn("?", body)

    def test_agda_signatures(self):
        text = read(AGDA)
        for sig in ("rank-laderman : RankLE₃ 3 23",
                    "rank-lower-laderman : 3 * 3 ≤ 23",
                    "laderman-saving : ∀ p q → 0 < q → 20 * q ≤ 7 * p → Saving₃ p q",
                    "laderman-not-below : ∀ p q → 6 * p < 17 * q → (23 ^ q) < (3 ^ p) → ⊥",
                    "rank-mixed : RankLE₃ 6 161",
                    "cert-laderman : 3 ^ 17 ≤ 23 ^ 6",
                    "cert-laderman-strict : 23 ^ 7 < 3 ^ 20",
                    "saving-laderman-20-7 : Saving₃ 20 7"):
            self.assertIn(sig, text, sig)

    def test_agda_clause_counts(self):
        text = read(AGDA)
        n_tab = len(re.findall(r"^(raL|rbL|rcL) \((fzero|fsuc)", text, re.M))
        n_eq = len(re.findall(r"^rank-eqL \(", text, re.M))
        self.assertEqual(n_tab, 621)   # 3 × 23 门 × 9 位置
        self.assertEqual(n_eq, 81)     # 9 × 9 (x,y), 各含 9 分支 z

    def test_agda_tables_match_oracle(self):
        """Agda 表子句与 oracle 表逐字一致（发射不失真; 逐字构造期望行断言存在）"""
        mod = self.mod
        trit = {0: "T₀", 1: "T₁", -1: "T₂"}
        lines = set(read(AGDA).split("\n"))
        for name, M in (("raL", mod.LAD["U"]), ("rbL", mod.LAD["V"]),
                        ("rcL", mod.LAD["W"])):
            for k in range(23):
                kpat = "fzero"
                for _ in range(k):
                    kpat = "fsuc (" + kpat + ")"
                for pos in range(9):
                    i, j = divmod(pos, 3)
                    ipat = ["fzero", "fsuc fzero", "fsuc (fsuc fzero)"][i]
                    jpat = ["fzero", "fsuc fzero", "fsuc (fsuc fzero)"][j]
                    expected = f"{name} ({kpat}) ({ipat} , {jpat}) = {trit[M[pos][k]]}"
                    self.assertIn(expected, lines, (name, k, i, j))
        # 总行数火计: 每张表 207 行子句
        text = read(AGDA)
        for name in ("raL", "rbL", "rcL"):
            n = sum(1 for ln in lines if ln.startswith(name + " ("))
            self.assertEqual(n, 207, name)

    # ---- 4. TriRV C 件 -------------------------------------------------------

    def test_trirv_no_bitops(self):
        """C 三值方言铁律: 代码区（去注释后）不得出现 & | ^ ~ << >>"""
        text = read(TRIRV)
        body = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
        body = "\n".join(line.split("//")[0] for line in body.split("\n"))
        for bad in ("&", "|", "^", "~", "<<", ">>"):
            self.assertNotIn(bad, body, bad)

    def test_trirv_pk_matches_oracle(self):
        """PK 打包表解包后与 oracle 的 Laderman 表一致（oracle ↔ VM 数据同源核对）"""
        mod = self.mod
        text = read(TRIRV)
        nums = re.search(r"int PK\[69\] = \{(.*?)\};", text, re.S).group(1)
        pk = [int(x) for x in re.findall(r"-?\d+", nums)]
        self.assertEqual(len(pk), 69)

        def unpack(v):
            out = []
            for _ in range(9):
                t = v - (v // 3) * 3
                if t == 2:
                    t = 0 - 1
                out.append(t)
                v = v // 3
            return out

        for name, M, off in (("U", mod.LAD["U"], 0), ("V", mod.LAD["V"], 23),
                             ("W", mod.LAD["W"], 46)):
            for k in range(23):
                row = unpack(pk[off + k])
                for pos in range(9):
                    self.assertEqual(row[pos], M[pos][k], (name, k, pos))

    def test_trirv_expected_exit_codes(self):
        """正件返回 0; 负控（PK[12] 最低位 2->0）返回 66 —— 双侧预言都由 oracle 侧模拟核对"""
        mod = self.mod

        def pack(M, k):
            v = 0
            for pos in range(9):
                v += (M[pos][k] % 3) * (3 ** pos)
            return v

        def simulate(pklist):
            def unpack(v):
                out = []
                for _ in range(9):
                    t = v - (v // 3) * 3
                    if t == 2:
                        t = 0 - 1
                # noqa 下一行才是 append（保持与 C 的解包次序一致）
                    out.append(t)
                    v = v // 3
                return out
            U = [[0] * 23 for _ in range(9)]
            V = [[0] * 23 for _ in range(9)]
            W = [[0] * 23 for _ in range(9)]
            for k in range(23):
                u = unpack(pklist[k])
                v = unpack(pklist[23 + k])
                w = unpack(pklist[46 + k])
                for pos in range(9):
                    U[pos][k] = u[pos]
                    V[pos][k] = v[pos]
                    W[pos][k] = w[pos]
            return mod.check_scheme(U, V, W, lambda x: x % 3)

        pk = [pack(mod.LAD["U"], k) for k in range(23)] \
            + [pack(mod.LAD["V"], k) for k in range(23)] \
            + [pack(mod.LAD["W"], k) for k in range(23)]
        bad, hits, fires, _ = simulate(pk)
        self.assertEqual((bad, hits, fires), (0, 27, 27))
        pkc = list(pk)
        pkc[12] -= 2
        bad, hits, fires, _ = simulate(pkc)
        self.assertEqual(bad * 4 + (27 - hits) * 2 + (fires - 27), 66)


if __name__ == "__main__":
    unittest.main()
