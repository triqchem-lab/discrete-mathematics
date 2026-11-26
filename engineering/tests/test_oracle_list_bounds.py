#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""ListBounds oracle 的回归测试（unittest, 零外部依赖）

对应:
  · oracle : engineering/oracle_list_bounds.py
  · Agda   : src/Sovereign/Algebra/LinearAlgebra/ListBounds.agda
             ★ lb-incompatible / ★ lb-incompatible-lists（0 postulate）
  · Lean   : OAI/LinearAlgebra/MatrixExponent/ListBounds.lean + Iteration.lean:76 `incompatible`

本测试不重证任何定理（裁决在 Agda 内核）; 它守住三件事:
  1. oracle 的 10 个核对函数全部通过, 且**非空转**（触发计数 > 0）;
  2. Agda 件在盘上、两个主定理的签名原样在、零 postulate、零 REWRITE 规则;
  3. oracle 里照抄的参数配方（N0、half、J、rn）与 Agda 主定理的文字一致（防两轨漂移）。
"""

import importlib.util
import os
import re
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
ORACLE = os.path.join(ROOT, "engineering", "oracle_list_bounds.py")
AGDA = os.path.join(ROOT, "src", "Sovereign", "Algebra", "LinearAlgebra", "ListBounds.agda")


def load_oracle():
    spec = importlib.util.spec_from_file_location("oracle_list_bounds", ORACLE)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def read_agda():
    with open(AGDA, encoding="utf-8") as fh:
        return fh.read()


class OracleListBounds(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.o = load_oracle()
        cls.src = read_agda()

    # ---- 1. oracle 十项全过, 且非空转 --------------------------------------
    def test_A_growth(self):
        tested, thr = self.o.check_growth(k_max=5, span=30)
        self.assertGreater(tested, 0)
        for k, used, w0 in thr:
            self.assertEqual(used, 2 ** (k + 4))
            self.assertLessEqual(w0, used)        # 采用的阈值不小于实测最小阈值

    def test_B_half(self):
        self.assertEqual(self.o.check_half(200), 201)

    def test_C_lin_exp(self):
        self.assertGreater(self.o.check_lin_exp(k_max=3, d_max=10), 0)

    def test_D_step_non_vacuous(self):
        tested, fires = self.o.check_step(W_max=7, n_max=2, t_max=2, extra=(0, 1, 5))
        self.assertGreater(tested, 0)
        self.assertEqual(tested, fires)           # 每个样本的前提都成立（首版曾空转）

    def test_E_rn_pkg(self):
        self.assertGreater(self.o.check_rn_pkg(bound=5), 0)

    def test_F_iteration_reaches_contradiction(self):
        res = self.o.check_iteration()
        self.assertTrue(res)
        for _case, _W, info in res:
            self.assertLessEqual(info["reached"], info["J"])

    def test_G_bridges_exact_rationals(self):
        t1, f1 = self.o.check_bridge_many(trials=120)
        self.assertGreater(f1, 0)                  # 前提成立的样本 > 0
        self.assertGreater(self.o.check_bridge_seed(trials=100), 0)
        t3, f3 = self.o.check_bridge_comp(trials=60)
        self.assertEqual(t3, f3)

    def test_H_h_bridge(self):
        w0, _ = self.o.check_h_bridge(w_max=400)
        self.assertLessEqual(w0, 3)

    def test_I_nonvacuity(self):
        tested = self.o.check_nonvacuity(w_max=10)
        self.assertGreater(tested, 0)

    # ---- 2. Agda 件的完整性（源级） -----------------------------------------
    def test_agda_file_present_and_clean(self):
        self.assertIn("module Sovereign.Algebra.LinearAlgebra.ListBounds where", self.src)
        self.assertIsNone(re.search(r"^\s*postulate\b", self.src, re.M))
        self.assertNotIn("{-# REWRITE", self.src)
        # 不依赖任何 Sovereign 模块（纯标准库）
        self.assertIsNone(re.search(r"^import Sovereign", self.src, re.M))

    def test_agda_main_theorems_present(self):
        self.assertRegex(self.src, r"(?m)^lb-incompatible :\s")
        self.assertRegex(self.src, r"(?m)^lb-incompatible-lists :\s")
        # 主定理的四条假设与结论 ⊥
        sig = re.search(r"lb-incompatible :[\s\S]*?→ ⊥", self.src).group(0)
        for name in ("lb-Grow N H", "lb-Seed P N", "lb-Many P N", "lb-Comp P N H"):
            self.assertIn(name, sig)

    def test_agda_nonvacuity_witnesses_present(self):
        # 四个一致性见证 + 四条「缺一不可」
        for name in ("lb-consistent-SMG", "lb-consistent-SCG", "lb-consistent-MCG", "lb-consistent-SMC",
                     "lb-necessary-C", "lb-necessary-M", "lb-necessary-S", "lb-necessary-G"):
            self.assertRegex(self.src, r"(?m)^%s :" % name, name)

    # ---- 3. 两轨的参数配方一致（防漂移） -------------------------------------
    def test_recipe_matches_agda_text(self):
        # 主定理里的参数配方（逐字）
        self.assertIn("W = rest + c₁ + 6", self.src)                     # W ≥ 6
        self.assertIn("w = W ^ (16 * q * G)", self.src)                  # w = W^N0, N0 = 16qG
        self.assertIn("lb-many-at W (16 * q * G) (16 * G * p)", self.src)
        self.assertIn("lb-comp-at P W (16 * q * G) rn", self.src)
        self.assertIn("2 * rn * G ≤ 16 * q * G * g", self.src)           # rn 的第一条侧条件
        self.assertIn("rn + 1 ≤ 8 * G * p", self.src)                    # rn 的第二条侧条件
        self.assertIn("lb-final W (8 * G * p) rn (16 * q * G)", self.src)  # half = 8Gp
        self.assertIn("3 * (16 * q * G) + 16 * G * p", self.src)         # J = 3N0 + 16Gp
        self.assertIn("lb-pow-ge (16 * q * G) h1W h1N0", self.src)
        # oracle 的配方
        o = self.o
        q, g, p, G = 2, 3, 5, 7
        N0, half, J = 16 * q * G, 8 * G * p, 3 * 16 * q * G + 16 * G * p
        info = o.simulate_iteration(q, g, p, G, 6, 2)
        self.assertEqual((info["N0"], info["half"], info["J"]), (N0, half, J))
        self.assertEqual(o.list_bits(q), 2 * q * 2 ** q)                 # Lean: listBits w = 2 * w * 2 ^ w


if __name__ == "__main__":
    unittest.main(verbosity=2)
