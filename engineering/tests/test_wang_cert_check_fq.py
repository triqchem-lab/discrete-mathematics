#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_cert_check_fq(通用域核对器)与 forced_fq C 内核的回归测试(unittest, 零外部依赖)

对应:
  · engineering/wang_cert_check_fq.py: 素域通用版独立核对器(GF(3) 路径)
  · engineering/forced_fq_c/forced_fq.c: Hopcroft–Kerr 引理 2 下界的独立 C 内核(多线程)
  · 上游证书: wcgbg/tensor-rank-lower-bound 的 F₂ q02_n333(/tmp 克隆易失, 缺失时跳过)

守住:
  1. C 内核对 F₂ 证书全部 forced 轨道算出的界与声明逐一相等(独立实现对拍);
  2. F₃ 域运算: 规范 RREF、矩阵逆、|GL(3,3)| = 11232、极小约束枚举;
  3. F₃ 证书在盘时(WANG_F3_CERT)的全量核对。
"""

import importlib.util
import os
import subprocess
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
FQ = os.path.join(ROOT, "engineering", "wang_cert_check_fq.py")
BASE = os.path.join(ROOT, "engineering", "wang_cert_check.py")
HELPER_SRC = os.path.join(ROOT, "engineering", "forced_fq_c", "forced_fq.c")
HELPER = os.path.join(ROOT, "engineering", "forced_fq_c", "forced_fq")
F2_CERT = "/tmp/wang-tensor-rank/real_cert_matrix_q02_n333.pb.txt"


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def ensure_helper():
    if not os.path.exists(HELPER) or os.path.getmtime(HELPER) < os.path.getmtime(HELPER_SRC):
        subprocess.run(["cc", "-O3", "-pthread", "-o", HELPER, HELPER_SRC], check=True)
    return HELPER


class ForcedKernelF2(unittest.TestCase):
    """C 内核在 F₂ 证书上的交叉验证: computed == claim, 逐一相等"""

    @unittest.skipUnless(os.path.exists(F2_CERT), "F₂ 证书未克隆(/tmp 易失)")
    def test_all_f2_forced_orbits_match_claim(self):
        helper = ensure_helper()
        base = load(BASE, "wang_cert_check")
        cert = base.parse_certificate(F2_CERT)
        forced = [o for o in cert["orbits"] if o["kind"] == "forced"]
        self.assertEqual(len(forced), 14)          # 前提火计: 非空转
        for o in forced:
            rows = base.rows_from_bytes(b"".join(o["raw_rows"]), 9)
            inp = f"2 {o['projection_type']} {len(rows)} {' '.join(map(str, rows))} {o['rank_lower_bound']}\n"
            out = subprocess.run([helper], input=inp, capture_output=True, text=True, check=True).stdout
            computed = int(out.split()[1])
            self.assertEqual(computed, o["rank_lower_bound"], (o["index"], out))

    def test_kernel_rejects_inflated_claim(self):
        """负控制: 把 orbit 5 的声明抬高, claim_ok 必须为 0(computed 仍为 9)"""
        helper = ensure_helper()
        out = subprocess.run([helper], input="2 1 7 1 2 4 8 16 64 160 16\n",
                             capture_output=True, text=True, check=True).stdout
        # 输出: computed <界> bit_width <bw> iterations <num> claim_ok <0|1>
        self.assertEqual(int(out.split()[1]), 9)
        self.assertEqual(out.split()[3], "9")
        self.assertEqual(out.split()[5], "512")
        self.assertEqual(out.split()[7], "0")


class FqFieldOps(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fq = load(FQ, "wang_cert_check_fq")
        cls.fq.P = 3

    def test_rref_matches_convention(self):
        fq = self.fq
        # 基 3 打包: e0 = 1, e1 = 3, e0 + 2·e2 = 1 + 2·9 → 秩 3, 规范化后主元为 1
        rows = [1, 3, 1 + 2 * 9]
        r, rank = fq.rref_fq(rows, 9)
        self.assertEqual(rank, 3)
        self.assertEqual(fq.is_canonical_rref_fq(r, 9), True)
        # 相关行: e0, 2·e0, e0 + 2·e2 → 秩 2, 零行落在最前
        r2, rank2 = fq.rref_fq([1, 2, 1 + 2 * 9], 9)
        self.assertEqual((rank2, r2), (2, [0, 1, 9]))
        # 原始行已规范时幂等
        self.assertEqual(fq.is_canonical_rref_fq(r, 9), fq.is_canonical_rref_fq(fq.rref_fq(r, 9)[0], 9))

    def test_gl3_order(self):
        self.assertEqual(len(self.fq.gl_set()), 11232)

    def test_mat_inverse(self):
        fq = self.fq
        ident = sum(3 ** (i * 3 + i) for i in range(3))
        a = 1 + 3 ** 4 + 2 * 3 ** 8  # diag(1,1,2) 可逆
        self.assertEqual(fq.mat_mul_fq(a, fq.mat_inv_fq(a)), ident)
        self.assertIsNone(fq.mat_inv_fq(0))

    def test_minimal_constraints_shape(self):
        fq = self.fq
        # 基无约束: 极小约束 = 首项为 1 的全部向量
        minimal = fq.build_minimal_fq([])
        self.assertEqual(len(minimal), (3 ** 9 - 1) // 2)   # 每个一维子空间一个代表
        for v in minimal:
            self.assertEqual(fq.digit(v, fq.leading_idx(v, 9)), 1)


class ForcedViaCParsing(unittest.TestCase):
    """forced_via_c 必须返回内核的 computed 字段, 而不是行尾的 claim_ok 标志。

    2026-11-27 实测: 旧实现取 `split()[-1]`, 把 F₃ dim-7 轨道的 `claim_ok 1` 当成了界,
    于是「forced 1 < 9」假警报。数值 9 来自 C++ 框架与 C 内核两个独立实现的一致结果。
    """

    # F₃ 枚举器输出的 dim-7 代表(index 5): e0 e1 e2 e3 e4 e6, e7 + e5; 投影 1 的枚举量 3^9。
    ROWS_F3 = [1, 3, 9, 27, 81, 729, 2430]

    @classmethod
    def setUpClass(cls):
        cls.helper = ensure_helper()
        cls.fq = load(FQ, "wang_cert_check_fq")
        cls.fq.P = 3

    def test_returns_computed_not_claim_ok_flag(self):
        got = self.fq.forced_via_c(self.ROWS_F3, 1, 9, helper=self.helper)
        self.assertEqual(got, 9)                       # 旧实现这里返回 1(claim_ok 标志)

    def test_inflated_claim_still_returns_computed(self):
        got = self.fq.forced_via_c(self.ROWS_F3, 1, 12, helper=self.helper)
        self.assertEqual(got, 9)                       # 声明抬高不改变复算值

    def test_pure_python_matches_c_kernel_on_f3(self):
        """独立实现的第二份(纯 Python)与 C 内核在 F₃ 上对拍(每个投影枚举 3^9, 实测约 7 s)。"""
        base = load(BASE, "wang_cert_check")
        fq = self.fq
        tensor = base.build_mul_tensor(3, 3, 3)
        for proj in (1, 2):
            t = fq.apply_constraints_fq(tensor, self.ROWS_F3, 9, 9, 9)
            t = fq.cyclic(t, 9, 9, 9) if proj == 1 else fq.cyclic(fq.cyclic(t, 9, 9, 9), 9, 9, 9)
            py, bw, iters = fq.forced_product_a_fq(t, 9, 9, 9)
            self.assertEqual((bw, iters), (9, 3 ** 9))
            self.assertEqual(py, fq.forced_via_c(self.ROWS_F3, proj, 0, helper=self.helper), (proj, py))


class BacktrackingKernel(unittest.TestCase):
    """回溯证明的独立重放内核(bt_fq.c) vs 纯 Python 重放: 合成实例上的交叉验证 + 负控制。

    不依赖 /tmp 里的证书。实例: 基取 8 维 e₀…e₆, e₈(规范 RREF), 极小约束只剩 e₇(3⁷ = 2187) 一条,
    所以第一层只有一个分支, 单条记录就是完整的证明。重放要求 claim ≤ popcount(mask) + 表中的界;
    轨道表的键用 Python 自己的 canonical_from_witness_fq 算——两个独立实现的矩阵运算必须一致,
    内核才会接受。
    """

    IDENT = 1 + 3 ** 4 + 3 ** 8          # 单位矩阵的打包数据
    SWAP01 = 3 ** 1 + 3 ** 3 + 3 ** 8    # 交换前两行的置换矩阵(E₁₂ + E₂₁ + E₃₃; 位 (i,j) 的权重 3^(3i+j))
    EL1 = 1 + 3 ** 1 + 3 ** 4 + 3 ** 8    # 初等矩阵 E₁₁ + E₁₂ + E₂₂ + E₃₃(第 0 行加上第 1 行)
    BASE8 = [1, 3, 9, 27, 81, 243, 729, 6561]
    EXT = BASE8 + [2187]

    @classmethod
    def setUpClass(cls):
        cls.fq = load(FQ, "wang_cert_check_fq")
        cls.fq.P = 3

    def both(self, claim, query, store, group_map):
        """返回 (内核是否接受, 内核给出的原因, 纯 Python 重放是否接受)。"""
        proof = {"sizes": [1], "masks": [1], "queries": [query], "stores": [store]}
        ok, _nodes, _leaves, reason = self.fq.bt_via_c(self.BASE8, claim, proof, dict(group_map))
        try:
            self.fq.make_backtracking_verifier_fq(self.BASE8, claim, proof, dict(group_map))()
            py_ok = True
        except AssertionError:
            py_ok = False
        return ok, reason, py_ok

    def key(self, query, store):
        return self.fq.canonical_from_witness_fq(self.EXT, query, store)

    def test_accept_and_both_implementations_agree(self):
        ok, reason, py_ok = self.both(6, self.IDENT, self.IDENT, {self.key(self.IDENT, self.IDENT): 5})
        self.assertTrue(ok, reason)
        self.assertTrue(py_ok)
        self.assertEqual(self.key(self.IDENT, self.IDENT), tuple(sorted(self.EXT)))

    def test_inflated_claim_rejected_by_both(self):
        ok, reason, py_ok = self.both(7, self.IDENT, self.IDENT, {self.key(self.IDENT, self.IDENT): 5})
        self.assertFalse(ok)
        self.assertEqual(reason, "claim > proved")
        self.assertFalse(py_ok)

    def test_witness_arithmetic_matches_python(self):
        """基取 7 维: 极小约束有 4 条(e₇, e₈, e₈+e₇, e₈+2e₇), 第一层 4 个分支各一条记录。
        扩展后的行组秩为 8 < 9, 规范形才真正依赖见证。每条记录的轨道表键由 Python 的
        canonical_from_witness_fq 算, 内核必须给出同一个规范形才会接受;
        把某一条的键换成未变换的行组, 两边都必须拒绝。"""
        base7 = [1, 3, 9, 27, 81, 243, 729]
        minimal7 = [2187, 6561, 8748, 10935]
        witnesses = [(self.IDENT, self.IDENT), (self.EL1, self.IDENT), (self.IDENT, self.EL1),
                     (self.SWAP01, self.EL1)]
        keys = [self.fq.canonical_from_witness_fq(base7 + [m], q, s)
                for m, (q, s) in zip(minimal7, witnesses)]
        self.assertTrue(all(k != tuple(sorted(base7 + [m])) for k, m in zip(keys, minimal7[1:])))
        proof = {"sizes": [1, 1, 1, 1], "masks": [1, 1, 1, 1],
                 "queries": [q for q, _ in witnesses], "stores": [s for _, s in witnesses]}
        group_map = dict(zip(keys, [5, 6, 7, 8]))

        def both(claim, gmap):
            ok, nodes, leaves, reason = self.fq.bt_via_c(base7, claim, proof, dict(gmap))
            try:
                self.fq.make_backtracking_verifier_fq(base7, claim, proof, dict(gmap))()
                py_ok = True
            except AssertionError:
                py_ok = False
            return ok, nodes, leaves, reason, py_ok

        ok, nodes, leaves, reason, py_ok = both(6, group_map)      # claim ≤ 1 + min(5,6,7,8)
        self.assertTrue(ok, reason)
        self.assertTrue(py_ok)
        self.assertEqual((nodes, leaves), (5, 4))
        ok, _n, _l, reason, py_ok = both(7, group_map)
        self.assertFalse(ok)
        self.assertEqual(reason, "claim > proved")
        self.assertFalse(py_ok)
        wrong = dict(group_map)
        del wrong[keys[2]]                              # 把第 3 条记录的键换成「未变换的行组」
        wrong[tuple(sorted(base7 + [minimal7[2]]))] = 7
        ok, _n, _l, reason, py_ok = both(6, wrong)
        self.assertFalse(ok)
        self.assertEqual(reason, "leaf canonical not in map")
        self.assertFalse(py_ok)

    def test_transpose_witness(self):
        """query 带 transpose 标志: 全体单位矩阵的集合在转置下不变 ⟹ 与单位见证同一个键。"""
        q = self.IDENT | (1 << 16)
        ok, reason, py_ok = self.both(6, q, self.IDENT, {tuple(sorted(self.EXT)): 5})
        self.assertTrue(ok, reason)
        self.assertTrue(py_ok)

    def test_empty_trace_rejected(self):
        proof = {"sizes": [], "masks": [], "queries": [], "stores": []}
        ok, _n, _l, reason = self.fq.bt_via_c(self.BASE8, 6, proof, {tuple(sorted(self.EXT)): 5})
        self.assertFalse(ok)
        self.assertEqual(reason, "empty trace")
        with self.assertRaises(AssertionError):
            self.fq.make_backtracking_verifier_fq(self.BASE8, 6, proof, {tuple(sorted(self.EXT)): 5})()

    def test_singular_witness_rejected(self):
        """store 取奇异矩阵(全零): 内核以「见证不在对称群里」拒绝。"""
        ok, reason, _py = self.both(6, self.IDENT, 0, {tuple(sorted(self.EXT)): 5})
        self.assertFalse(ok)
        self.assertEqual(reason, "witness not in the symmetry group")


class FqFullCheck(unittest.TestCase):
    @unittest.skipUnless(os.environ.get("WANG_F3_CERT"), "设 WANG_F3_CERT 指向 F₃ 证书")
    def test_full_f3_certificate(self):
        ensure_helper()
        fq = load(FQ, "wang_cert_check_fq")
        import io
        from contextlib import redirect_stdout
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = fq.main([FQ, os.environ["WANG_F3_CERT"]])
        self.assertEqual(rc, 0)
        self.assertIn("OK.", buf.getvalue())


if __name__ == "__main__":
    unittest.main()
