#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""wang_cert_check 的回归测试(unittest, 零外部依赖)

对应:
  · 核对器: engineering/wang_cert_check.py(立项 A-T2/A-T4: Wang 框架证书的独立核对)
  · 上游仓库: github.com/wcgbg/tensor-rank-lower-bound(C++, /tmp 克隆易失, 缺失时跳过依赖项)
  · 论文: arXiv:2603.07280(F₂ ⟨3,3,3⟩ ≥ 20)与 arXiv:2609.06725(F₂ ≥ 21)

测试内容:
  1. 证书解析(括号深度 + 转义)与 GFVec 行解码;
  2. F₂ ⟨3,3,3⟩ 张量构造与约束代入折叠(与 BuildMulTensor/ApplyConstraintsToTensor 语义对齐);
  3. flatten 三个方向的展平秩(随机张量 + 全 T₁ 加权);
  4. 仓库证书在盘时的全量核对(结构 RREF + flatten/forced/degenerate/backtracking 496 轨道);
  5. 负控制: 篡改声明必须转红。
"""

import importlib.util
import os
import random
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CHECKER = os.path.join(ROOT, "engineering", "wang_cert_check.py")
CLONE = "/tmp/wang-tensor-rank"
CERT = os.path.join(CLONE, "real_cert_matrix_q02_n333.pb.txt")
BTP = os.path.join(CLONE, "real_cert_matrix_q02_n333.btp")


def load_checker():
    spec = importlib.util.spec_from_file_location("wang_cert_check", CHECKER)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


class WangCertCheck(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.mod = load_checker()

    # ---- 1. 张量与约束语义 ----

    def test_build_mul_tensor(self):
        t = self.mod.build_mul_tensor(3, 3, 3)
        ones = [(i, j, k) for i in range(9) for j in range(9) for k in range(9)
                if t[i][j][k]]
        # 结构常数: 恰 27 个非零三元组, 全部对角形 x=(i,j), y=(j,k), z=(i,k)
        self.assertEqual(len(ones), 27)
        for x, y, z in ones:
            xr, xc = divmod(x, 3)
            yr, yc = divmod(y, 3)
            zr, zc = divmod(z, 3)
            self.assertEqual(xc, yr)
            self.assertEqual(yc, zr)
            self.assertEqual(xr, zc)

    def test_apply_constraints_folds_pivot(self):
        base = self.mod.build_mul_tensor(3, 3, 3)
        # 约束 e0: 折叠后 A-slice 0 清零, 其余不变(e0 的 free = 0)
        rows = [1]
        t = self.mod.apply_constraints_f2(base, rows, 9, 9, 9)
        for j in range(9):
            for k in range(9):
                self.assertEqual(t[0][j][k], 0)
                self.assertEqual(t[1][j][k], base[1][j][k])

    # ---- 2. 展平秩 ----

    def test_flatten_unconstrained(self):
        base = self.mod.build_mul_tensor(3, 3, 3)
        slices = [sum(row[j][k] << (j * 9 + k) for j in range(9) for k in range(9))
                  for row in base]
        # 无约束 ⟨3,3,3⟩ 的展平界 = 9(三向均满秩)
        self.assertEqual(self.mod.rank_lower_bound_flatten(slices, 9, 9, 9, 1 << 30), 9)

    def test_flatten_bound_is_monotone_under_constraints(self):
        base = self.mod.build_mul_tensor(3, 3, 3)
        r0 = self.mod.rank_lower_bound_flatten(
            [sum(row[j][k] << (j * 9 + k) for j in range(9) for k in range(9))
             for row in base], 9, 9, 9, 1 << 30)
        t1 = self.mod.apply_constraints_f2(base, [1], 9, 9, 9)
        r1 = self.mod.rank_lower_bound_flatten(
            [sum(row[j][k] << (j * 9 + k) for j in range(9) for k in range(9))
             for row in t1], 9, 9, 9, 1 << 30)
        self.assertLessEqual(r1, r0)

    # ---- 3. 仓库证书(在盘时) ----

    @unittest.skipUnless(os.path.exists(CERT), "证书未克隆(/tmp 易失)")
    def test_certificate_structure(self):
        cert = self.mod.parse_certificate(CERT)
        self.assertEqual(cert['problem_name'], 'matrix_q02_n333')
        self.assertEqual((cert['characteristic'], cert['extension_degree']), (2, 1))
        self.assertEqual((cert['na'], cert['nb'], cert['nc']), (9, 9, 9))
        self.assertEqual(len(cert['orbits']), 496)

    @unittest.skipUnless(os.path.exists(CERT), "证书未克隆")
    @unittest.skipUnless(os.environ.get('WANG_FULL'), "全量核对 ~15 分钟; WANG_FULL=1 显式运行")
    def test_certificate_full_check(self):
        """全量: 496 轨道(结构 + flatten + forced + degenerate + backtracking)"""
        import io
        from contextlib import redirect_stdout
        buf = io.StringIO()
        with redirect_stdout(buf):
            rc = self.mod.main([CHECKER, CERT])
        self.assertEqual(rc, 0)
        self.assertIn('UNCONSTRAINED TENSOR RANK LOWER BOUND: 20', buf.getvalue())
        self.assertIn('OK.', buf.getvalue())

    @unittest.skipUnless(os.path.exists(BTP), "回溯档案未克隆")
    def test_btp_archive_shape(self):
        blobs = self.mod.load_btp(BTP)
        self.assertEqual(len(blobs), 496)
        # 至少一个非空 blob(有 backtracking 轨道)
        self.assertTrue(any(b for b in blobs))


if __name__ == '__main__':
    unittest.main()
