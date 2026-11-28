#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""M25 / M26 / M27 oracle 的回归测试（unittest, 零外部依赖）

对应:
  · oracle : engineering/oracle_tensor_rank_capacity_gf3.py
  · Agda   : src/Sovereign/Algebra/LinearAlgebra/TensorRankCapacityGF3.agda   (M25)
             ★ rank-drops / ★ capacity / ★ capacity-bound / capacity-span
             src/Sovereign/Algebra/LinearAlgebra/TensorRankProfileGF3.agda    (M26)
             ★★ profiles-19（r = 19、Σ 秩 = 27 恰五种）/ profiles-23
             src/Sovereign/Algebra/LinearAlgebra/TensorRankBudgetGF3.agda     (M27)
             ★★ rank-budget : Pieces n N r (ra ρ) → n * n * n ≤ N

本测试不重证任何定理（裁决在 Agda 内核）; 它守住四件事:
  1. oracle 全部通过, 且**非空转**（触发计数 > 0）;
  2. oracle 有区分力: 丢错项必须报不一致; 分割展平的 δ 结构被破坏必须报失配;
     标准分解的输出因子写反必须报失配（首版我就写反过, 是 oracle 抓到的）;
  3. Agda 件在盘上、主定理的签名原样在、零 postulate、零 REWRITE 规则、零洞;
  4. 两轨的数字一致: M27 的哨兵是 Strassen 的 8 个片块 = 2³; M26 的 19 / 27 / 五种剖面。
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
ORACLE = os.path.join(ROOT, "engineering", "oracle_tensor_rank_capacity_gf3.py")
LIN = os.path.join(ROOT, "src", "Sovereign", "Algebra", "LinearAlgebra")
AGDA_CAP = os.path.join(LIN, "TensorRankCapacityGF3.agda")
AGDA_PROF = os.path.join(LIN, "TensorRankProfileGF3.agda")
AGDA_BUD = os.path.join(LIN, "TensorRankBudgetGF3.agda")


def load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_tensor_rank_capacity_gf3", ORACLE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read(path):
    with open(path, encoding="utf-8") as fh:
        return fh.read()


def strip_comments(text):
    return "\n".join(line.split("--")[0] for line in text.split("\n"))


def sig_in(text, name):
    """顶层签名 `name … :` 原样在（不看注释）"""
    # 名字后面不能再接标识符字符（\b 在 ≤ 这种非单词字符后面不成立, 所以用否定先行）
    return re.search(r"^(record\s+)?%s(?![A-Za-z0-9₀-₉′ʳˡᵀ₁₂₃])[^:=]*:" % re.escape(name), strip_comments(text), re.M) is not None


class CapacityProfileBudgetOracle(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.mod = load_oracle()

    # ---- 1. 全部通过 + 非空转 ------------------------------------------------

    def test_main_all_pass(self):
        buf = io.StringIO()
        argv = sys.argv
        sys.argv = ["oracle_tensor_rank_capacity_gf3.py"]
        try:
            with redirect_stdout(buf):
                rc = self.mod.main()
        finally:
            sys.argv = argv
        out = buf.getvalue()
        self.assertEqual(rc, 0)
        self.assertIn("oracle: ALL_PASS", out)
        # 非空转: 每条判据的前提都真的触发过
        self.assertRegex(out, r"丢掉落在 W 里的项后余和 = T\): (\d+)/\1 ")
        self.assertGreater(int(re.search(r"随机分解 (\d+) 个", out).group(1)), 0)
        self.assertGreater(int(re.search(r"负对照\(丢掉一个不在 W 里[^)]*\) (\d+) 次", out).group(1)), 0)
        self.assertGreater(int(re.search(r"不同的非零首因子 (\d+) 个", out).group(1)), 0)
        self.assertIn("违反 N + L ≤ r 的 0 个", out)
        self.assertIn("不一致的 (v,y,z) 0 个", out)
        self.assertRegex(out, r"（其中 (\d+) 组非空）")          # 全角括号
        self.assertIn("r = 19, n = 3 恰 5 个", out)
        self.assertIn("Σ rank = 31 ≥ n³ = 27", out)
        self.assertIn("Σ rank = 8 ≥ n³ = 8（取等）", out)
        self.assertGreaterEqual(out.count("（取等）"), 3)       # Strassen + 两个标准分解

    def test_profiles_exact(self):
        m = self.mod
        self.assertEqual(m.profiles_by_bruteforce(19, 3),
                         [(11, 8, 0), (12, 6, 1), (13, 4, 2), (14, 2, 3), (15, 0, 4)])
        self.assertEqual(m.profiles_by_formula(19, 3), m.profiles_by_bruteforce(19, 3))
        self.assertEqual(m.profiles_by_bruteforce(23, 3), [(19, 4, 0), (20, 2, 1), (21, 0, 2)])
        self.assertEqual(m.profiles_by_bruteforce(7, 2), [(6, 1, 0)])          # Strassen 的剖面, Δ = 0
        self.assertEqual(m.profiles_by_bruteforce(9, 2), [])                    # r > n³: 没有剖面
        # Laderman 的 (17,4,2): Σ 秩 31, 不是 27
        self.assertNotIn((17, 4, 2), m.profiles_by_bruteforce(23, 3))

    def test_budget_values(self):
        m = self.mod
        bad, N, cube = m.check_budget(*m.laderman())
        self.assertEqual((bad, N, cube), (0, 31, 27))
        bad, N, cube = m.check_budget(*m.strassen())
        self.assertEqual((bad, N, cube), (0, 8, 8))
        bad, N, cube = m.check_budget(*m.schoolbook(3))
        self.assertEqual((bad, N, cube), (0, 27, 27))

    # ---- 2. 区分力（负对照）--------------------------------------------------

    def test_capacity_reports_wrong_drop(self):
        """丢掉一个不在 W 里、在 V 上非零的项: 余和必须与 T 不一致（至少一例）"""
        import random
        m = self.mod
        rng = random.Random(7)
        found = 0
        for _ in range(50):
            nx, ny, nz, r = 3, 2, 2, 5
            a = [[rng.randrange(3) for _ in range(nx)] for _ in range(r)]
            b = [[rng.randrange(3) for _ in range(ny)] for _ in range(r)]
            c = [[rng.randrange(3) for _ in range(nz)] for _ in range(r)]
            xstar = rng.randrange(nx)
            for t in range(r):
                a[t][xstar] = 0 if t < 3 else a[t][xstar]
            if a[4][xstar] == 0:
                a[4][xstar] = 1
            V = [x for x in range(nx) if all(a[t][x] == 0 for t in range(3))]
            T = lambda x, y, z: sum(a[t][x] * b[t][y] * c[t][z] for t in range(r)) % 3
            R = lambda x, y, z: sum(a[t][x] * b[t][y] * c[t][z] for t in range(3)) % 3
            if any(R(x, y, z) != T(x, y, z) for x in V for y in range(ny) for z in range(nz)):
                found += 1
        self.assertGreater(found, 0)

    def test_budget_reports_broken_decomposition(self):
        """把 Laderman 的一个系数改掉: 分割展平的 δ 结构必须被破坏"""
        m = self.mod
        A, B, C, n = m.laderman()
        A1 = [[row[:] for row in M] for M in A]
        A1[0][0][0] = (A1[0][0][0] + 1) % 3
        bad, _, _ = m.check_budget(A1, B, C, n)
        self.assertGreater(bad, 0)

    def test_budget_reports_transposed_output_factor(self):
        """标准分解把输出因子写成 E_ki（首版的错误）: 必须失配"""
        m = self.mod
        A, B, C, n = m.schoolbook(3)
        Ct = [[list(r) for r in zip(*M)] for M in C]          # 转置
        bad, _, _ = m.check_budget(A, B, Ct, n)
        self.assertGreater(bad, 0)

    # ---- 3. Agda 件: 在盘、签名在、零 postulate / REWRITE / 洞 -----------------

    def test_agda_files_and_signatures(self):
        cap, prof, bud = read(AGDA_CAP), read(AGDA_PROF), read(AGDA_BUD)
        for name in ("yesCnt", "rank-cons", "rank-drops", "capacity", "capacity-bound", "inSpan",
                     "capacity-span", "LowerBound"):
            self.assertTrue(sig_in(cap, name), name)
        for name in ("profile-Δ", "profile-param", "profile-n₃≤", "profiles-19", "profiles-23",
                     "laderman-not-Δ0", "strassen-Σrank"):
            self.assertTrue(sig_in(prof, name), name)
        for name in ("Pieces", "rank-budget"):
            self.assertTrue(sig_in(bud, name), name)
        for text in (cap, prof, bud):
            code = strip_comments(text)
            self.assertNotRegex(code, r"(?m)^\s*postulate\b")
            self.assertNotIn("{-# REWRITE", text)
            self.assertNotRegex(code, r"(?m)^\s*[^ \t-][^\n]*?\s\?\s*$")     # 顶层洞
        # 主定理的形状
        self.assertRegex(cap, r"capacity : \(X' : Set\) → ∀ \{X Y Z r\}")
        self.assertRegex(cap, r"LowerBound \(λ x' y z → T \(ι x'\) y z\) L →\s*\n\s*yesCnt P\? \+ L ≤ r")
        self.assertRegex(prof, r"profiles-19 : ∀ n₁ n₂ n₃ → n₁ \+ n₂ \+ n₃ ≡ 19 → n₁ \+ 2 \* n₂ \+ 3 \* n₃ ≡ 27 →")
        self.assertRegex(bud, r"Pieces n N r \(ra ρ\) → n \* n \* n ≤ N")

    def test_agda_profile_counts_match_oracle(self):
        prof = read(AGDA_PROF)
        code = strip_comments(prof)
        # profiles-19 的结论里恰好列出 oracle 的五种
        block19 = code[code.index("profiles-19 :"):code.index("profiles-23 :")]
        for (n1, n2, n3) in self.mod.profiles_by_bruteforce(19, 3):
            self.assertIn("n₁ ≡ %d × n₂ ≡ %d × n₃ ≡ %d" % (n1, n2, n3), block19)
        block23 = code[code.index("profiles-23 :"):code.index("strassen-Σrank :")]
        for (n1, n2, n3) in self.mod.profiles_by_bruteforce(23, 3):
            self.assertIn("n₁ ≡ %d × n₂ ≡ %d × n₃ ≡ %d" % (n1, n2, n3), block23)
        self.assertEqual(block19.count(" × n₃ ≡ "), 5)
        self.assertEqual(block23.count(" × n₃ ≡ "), 3)


if __name__ == "__main__":
    unittest.main()
