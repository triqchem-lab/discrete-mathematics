#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_capacity_probe.py 的回归测试(unittest, 零外部依赖)

对应 engineering/wang_capacity_probe.py（F₃ ⟨3,3,3⟩ 的「容量–剖面」探针, PROVEN §二十三）:
  · 容量表只读证书, 纯 Python, 任何机器都能跑;
  · 查表件 orbit_lookup（/tmp 易失, 缺失时跳过）在盘时跑四道验证与两条负对照。

守住:
  1. 证书 736 个轨道的界分布、r = 19 的容量表（cap_min / cap_max 逐维);
  2. Δ 的秩剖面算术（Δ = 0 恰 5 个剖面, Δ = 1 恰 5 个）;
  3. 纯 Python 的 RREF / 3×3 秩 / 矩阵求逆;
  4. 查表件: 全流程 ALL_PASS; 见证被改动后复核必须失败; 一条直线上 4 个点必须被报出。
"""

import importlib.util
import io
import os
import random
import unittest
from collections import Counter
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
SRC = os.path.join(ROOT, "engineering", "wang_capacity_probe.py")
BIN = os.environ.get("ORBIT_LOOKUP", "/tmp/wang-f3/orbit_lookup")


def load():
    spec = importlib.util.spec_from_file_location("wang_capacity_probe", SRC)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class CapacityTable(unittest.TestCase):
    """只读证书的部分"""

    def test_bound_histogram_matches_record(self):
        P = load()
        orbits = P.load_orbits()
        self.assertEqual(len(orbits), 736)
        hist = {d: Counter(o["bound"] for o in orbits if o["codim"] == d) for d in range(10)}
        self.assertEqual(hist, P.EXPECTED_HIST)

    def test_capacity_table_r19(self):
        P = load()
        tab = P.capacity_table(P.load_orbits(), 19)
        self.assertEqual([tab[d]["capmin"] for d in range(1, 9)], [3, 4, 4, 5, 6, 6, 7, 10])
        self.assertEqual([tab[d]["capmax"] for d in range(1, 9)], [3, 4, 6, 7, 9, 10, 13, 16])
        self.assertEqual(tab[9]["capmin"], 19)          # 全空间: 余维 9 的界是 0

    def test_delta_profiles(self):
        P = load()
        prof = P.delta_profiles(19)
        self.assertEqual(prof[0], [(11, 8, 0), (12, 6, 1), (13, 4, 2), (14, 2, 3), (15, 0, 4)])
        self.assertEqual(prof[1], [(10, 9, 0), (11, 7, 1), (12, 5, 2), (13, 3, 3), (14, 1, 4)])
        self.assertEqual(min(prof), -8)                   # 19 项全秩 1

    def test_linear_algebra(self):
        P = load()
        I = [1, 0, 0, 0, 1, 0, 0, 0, 1]
        self.assertEqual(P.rank3(I), 3)
        self.assertEqual(P.rank3([1, 0, 0, 0, 0, 0, 0, 0, 0]), 1)
        self.assertEqual(P.rank3([0, 1, 0, 2, 0, 0, 0, 0, 0]), 2)
        b, rk = P.rref([I, [0] * 9, [1, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0], [2, 0, 0, 0, 2, 0, 0, 0, 2]])
        self.assertEqual(rk, 3)                        # 2I 与 I 相关, 零行丢弃
        self.assertTrue(P.in_span((2, 1, 0, 0, 1, 1, 0, 0, 1), b))     # (e₁+e₂) + I + e₆
        self.assertFalse(P.in_span((0, 0, 0, 1, 0, 0, 0, 0, 0), b))
        # 矩阵逆: J = [[0,1],[-1,0]] 的逆是 −J
        J = [[0, 1, 0], [2, 0, 0], [0, 0, 1]]
        self.assertEqual(P.mat_mul(J, P.mat_inv(J)), [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
        with self.assertRaises(StopIteration):      # 奇异输入没有逆: 直接抛（见证里的 R 必可逆）
            P.mat_inv([[1, 0, 0], [0, 0, 0], [0, 0, 1]])

    def test_bad_plane_representative_and_counts(self):
        """L = 12 的那个平面轨道（证书位置 17）: 代表束全可逆、行列式型、以及双计数（不需要查表件）"""
        P = load()
        orbits = P.load_orbits()
        bad = [o for o in orbits if o["codim"] == 7 and o["bound"] == 12]
        self.assertEqual([o["index"] for o in bad], [17])            # 平面 14 个轨道里恰 1 个是 L = 12
        basis = P.annihilator(bad[0]["rows"])                         # 约束行张成 7 维 W; 零化子 = 那个平面
        self.assertEqual(len(basis), 2)
        known = [(0, 2, 2, 1, 1, 0, 1, 0, 0), (0, 2, 0, 1, 0, 0, 0, 0, 1)]       # 022110100, 020100001
        self.assertEqual(P.rref(basis)[0], P.rref([list(k) for k in known])[0])   # 张成相同, 不绑死基的取法
        allinv, coef = P.pencil_facts(basis[0], basis[1])
        self.assertTrue(allinv)
        self.assertEqual(coef, {(3, 0): 1, (2, 1): 1, (1, 2): 2, (0, 3): 1})   # x³ + x²y + 2xy² + y³
        self.assertEqual(P.GL3, 11232)
        self.assertEqual(P.PLANES, 8069620)
        self.assertEqual(P.no_eigenvalue_count(), 3456)
        self.assertEqual(P.GL3 * 3456 // 48, 808704)                  # 每个平面 48 组有序基
        self.assertEqual(576 * P.GL3 // 8, 808704)                    # 过每个可逆向量 576 个, 每个平面 8 个可逆元素


@unittest.skipUnless(os.path.exists(BIN), "查表件未构建(/tmp 易失; bash engineering/wang_f3ext/build.sh 3 lookup …)")
class WithLookupTool(unittest.TestCase):
    """需要 orbit_lookup 二进制的部分"""

    def test_full_run_all_pass(self):
        P = load()
        buf = io.StringIO()
        with redirect_stdout(buf):
            res = P.run(BIN, seed=1)
        self.assertEqual(res, "ALL_PASS")
        out = buf.getvalue()
        self.assertIn("验证 1 自检: 736 条目 × 4 个随机群像, 失败 0", out)
        self.assertIn("验证 2 见证重放（Python 自己的群作用实现）: 60/60", out)
        self.assertIn("r = 23 候选 645 / 违规 0", out)
        self.assertIn("验证 5 L = 12 平面的结构", out)
        self.assertIn("这类平面 808704 个 (10.02%)", out)

    def test_planes_through_fixed_lines(self):
        """穷举过三条固定直线的全部 3280 个平面: 过奇异矩阵的从不取 L = 12, 过可逆矩阵的恰 576 个"""
        P = load()
        tool = P.LookupTool(BIN)
        try:
            ps = P.plane_structure(tool, P.load_orbits())
        finally:
            tool.close()
        self.assertEqual((ps["E11"][6], ps["E11"][9], ps["E11"][10], ps["E11"][12]), (152, 2552, 576, 0))
        self.assertEqual(ps["E11+E22"][12], 0)
        self.assertEqual(sum(ps["E11+E22"].values()), 3280)
        self.assertEqual(ps["I"][12], 576)
        self.assertEqual(sum(ps["I"].values()), 3280)

    def test_witness_tamper_fails(self):
        P = load()
        orbits = P.load_orbits()
        rng = random.Random(3)
        tool = P.LookupTool(BIN)
        try:
            qs = [P.random_subspace(rng, 7) for _ in range(5)]
            for q, (b, p, qe, se) in zip(qs, tool.ask(qs)):
                self.assertTrue(tool.witness_ok(q, b, p, qe, se, orbits))
                self.assertFalse(tool.witness_ok(q, b + 1, p, qe, se, orbits))            # 界改了
                self.assertFalse(tool.witness_ok(q, b, (p + 1) % 736, qe, se, orbits))    # 指向别的轨道
        finally:
            tool.close()

    def test_four_points_on_a_line_are_reported(self):
        P = load()
        rng = random.Random(5)
        pts = P.random_config(rng, 16)
        pts = [pts[0]] * 4 + pts[1:]                 # 19 个点, 第一条直线上 4 个
        tool = P.LookupTool(BIN)
        try:
            z, per_dim, viol = tool.config(19, pts)
            bound = tool.ask([[list(pts[0])]])[0][0]   # 这条直线的零化子（8 维）的证书界
        finally:
            tool.close()
        self.assertEqual(len(pts), 19)
        self.assertEqual(per_dim[1], (1, 1), "dim 1: 应恰一条候选直线、恰一处违规")
        self.assertEqual(z[1], 1 + sum(v for _, v in per_dim.values()) - per_dim[1][1], "违规总数 = 各维之和")
        self.assertEqual(bound, 16)                   # cap = 19 − 16 = 3 < N = 4

    def test_violation_total_equals_sum_over_dims(self):
        P = load()
        tool = P.LookupTool(BIN)
        try:
            z, per_dim, viol = tool.config(19, P.random_config(random.Random(9)))
        finally:
            tool.close()
        self.assertEqual(z[0], sum(c for c, _ in per_dim.values()))
        self.assertEqual(z[1], sum(v for _, v in per_dim.values()))
        self.assertGreater(z[1], 0)


if __name__ == "__main__":
    unittest.main()
