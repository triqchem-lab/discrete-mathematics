#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""TensorRankGF3 oracle 的回归测试（unittest, 零外部依赖）

对应:
  · oracle : engineering/oracle_tensor_rank_gf3.py
  · Agda   : src/Sovereign/Algebra/LinearAlgebra/TensorRankGF3.agda          (M16-A)
             ★ rank-strassen : RankLE₃ 2 7（M13 的七门 = 7 项秩分解）
             src/Sovereign/Algebra/LinearAlgebra/TensorRankFlattenGF3.agda   (M16-B)
             ★ rank-lower : ∀ n r → RankLE₃ n r → n * n ≤ r（计数证法）
  · Lean   : OAI/LinearAlgebra/MatrixExponent/RationalCircuits.lean `RankLE`
             OAI/LinearAlgebra/MatrixExponent/Flattening.lean:6 `rank_lower`

本测试不重证任何定理（裁决在 Agda 内核）; 它守住四件事:
  1. oracle 的核对函数全部通过, 且**非空转**（触发计数 > 0）;
  2. oracle 有区分力: 弄坏一个系数, 判据一必须报错（负控制）;
  3. Agda 件在盘上、两条主定理的签名原样在、零 postulate、零 REWRITE 规则、零洞;
  4. 两轨的「项数」一致: oracle 的 ALPHA/BETA/C 都是 7 行, Agda 主定理写的是 RankLE₃ 2 7。
"""

import importlib.util
import io
import os
import re
import sys
import unittest
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ORACLE = os.path.join(ROOT, "engineering", "oracle_tensor_rank_gf3.py")
AGDA_A = os.path.join(ROOT, "src", "Sovereign", "Algebra", "LinearAlgebra", "TensorRankGF3.agda")
AGDA_B = os.path.join(ROOT, "src", "Sovereign", "Algebra", "LinearAlgebra", "TensorRankFlattenGF3.agda")


def load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_tensor_rank_gf3", ORACLE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def strip_comments(text):
    return "\n".join(line.split("--")[0] for line in text.split("\n"))


class OracleTensorRankGF3(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.mod = load_oracle()

    # ---- 1. 全部通过 + 非空转 ------------------------------------------------

    def test_structure_constants(self):
        tested = self.mod.check_structure_constants()
        self.assertEqual(tested, 64)
        self.assertGreater(tested, 0)

    def test_matrices(self):
        tested = self.mod.check_matrices()
        self.assertEqual(tested, 6561 * 4)
        self.assertGreater(tested, 0)

    def test_two_paths_agree(self):
        tested = self.mod.check_two_paths_agree_on_basis()
        self.assertEqual(tested, 64)

    def test_span_construction_fires(self):
        basis, fires = self.mod.check_span_construction()
        self.assertEqual(basis, 16)          # 16 条标准基全部落在张成里
        self.assertEqual(fires, 400 * 4)     # 400 组随机 λ × 4 点, 原像全部复原

    def test_span_capacity_fires(self):
        tested, samples, cap_ok = self.mod.check_span_capacity(samples=200)
        self.assertEqual(samples, 200)       # r = 3 的 200 组生成元无一张出全部标准基
        self.assertEqual(cap_ok, 4)          # 对照: r = 4 时判别器报 4/4 在张成里
        self.assertEqual(tested, 200 + 1 + 5 * 12)

    def test_main_all_pass(self):
        buf = io.StringIO()
        argv = sys.argv
        sys.argv = ["oracle_tensor_rank_gf3.py"]
        try:
            with redirect_stdout(buf):
                rc = self.mod.main()
        finally:
            sys.argv = argv
        self.assertEqual(rc, 0)
        self.assertIn("ALL_PASS", buf.getvalue())

    # ---- 2. 负控制: oracle 有区分力 ------------------------------------------

    def test_negative_control_corrupted_beta(self):
        """把 BETA 的一个系数改掉, 判据一必须失败（否则「64 次成立」是空转）"""
        beta = self.mod.BETA
        old = beta[2][1]
        beta[2][1] = (old + 1) % 3
        try:
            with self.assertRaises(AssertionError):
                self.mod.check_structure_constants()
        finally:
            beta[2][1] = old
        self.assertEqual(self.mod.check_structure_constants(), 64)   # 复原后重新成立

    def test_negative_control_corrupted_output_coefficient(self):
        """把 C 的一行改掉, 判据二（走普通矩阵乘法的独立路径）必须失败"""
        c = self.mod.C
        old = c[1][3]
        c[1][3] = (old + 1) % 3
        try:
            with self.assertRaises(AssertionError):
                self.mod.check_matrices()
        finally:
            c[1][3] = old
        self.assertEqual(self.mod.check_matrices(), 6561 * 4)

    # ---- 3. Agda 件: 在盘、签名原样、零红线 -----------------------------------

    def test_agda_files_present(self):
        for p in (AGDA_A, AGDA_B):
            self.assertTrue(os.path.isfile(p), p)

    def test_agda_main_signatures(self):
        a = read(AGDA_A)
        b = read(AGDA_B)
        self.assertIn("rank-strassen : RankLE₃ 2 7", a)
        self.assertIn("ω₃-boundary : Set", a)
        self.assertIn("rank-lower : ∀ n r → RankLE₃ n r → n * n ≤ r", b)
        self.assertIn("check-lower-strassen : 2 * 2 ≤ 7", b)

    def test_agda_no_postulate_no_rewrite_no_hole(self):
        for p in (AGDA_A, AGDA_B):
            code = strip_comments(read(p))
            self.assertIsNone(re.search(r"^\s*postulate\b", code, re.M), p)
            self.assertNotIn("{-# REWRITE", code, p)
            self.assertNotIn("{!", code, p)
            self.assertIsNone(re.search(r"\s\?\s*$", code, re.M), p)

    # ---- 4. 两轨一致: 项数都是 7 ---------------------------------------------

    def test_term_counts_agree(self):
        self.assertEqual(len(self.mod.ALPHA), 7)
        self.assertEqual(len(self.mod.BETA), 7)
        self.assertEqual(len(self.mod.C), 7)
        for row in self.mod.ALPHA + self.mod.BETA + self.mod.C:
            self.assertEqual(len(row), 4)
            self.assertTrue(all(v in (0, 1, 2) for v in row))


if __name__ == "__main__":
    unittest.main()
