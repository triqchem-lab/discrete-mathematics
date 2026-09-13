"""
DC 交叉验证：Python 精确整数计算 ←→ Agda 定理
============================================================
方法论：先算后验证（zcode 提议，本项目既有双轨制的形式化）
  · Python 侧：枚举 / 核对 / 找反例 —— 这是**证据**，不是证明
  · Agda 侧：`Sovereign.Algebra.Pi4Homomorphism` /
             `Sovereign.Algebra.GroupTheory.DCInvolution` /
             `Sovereign.Algebra.GroupTheory.DCSigmaAut` /
             `Sovereign.Algebra.GroupTheory.DuodecClock` —— 唯一裁决

无信息截断要求（本文件同时验证）：
  · 载体必须保留 (幅度 Trit, 相位 AlphaPower) **两个分量**
  · 任何把相位 C₄ → C₂ 的投影都是非单射 = 结构性信息丢失，不得作为模型输入
  · Trit 语义必须用 Agda 索引语义 (T₀=0, T₁=1, T₂=2, ⊕=(a+b)%3)，
    不得混用项目 Python 层的 T0=-1/T1=0/T2=+1 标注（那是另一套标签）

零外部依赖；全整数精确运算；禁浮点。
"""

import unittest
import itertools

# ------------------------------------------------------------
# §1. Agda 侧语义的精确镜像
# ------------------------------------------------------------

MOD3 = 3
MOD4 = 4
MOD12 = 12

# Trit: Agda 索引语义
TRIT = (0, 1, 2)  # T₀, T₁, T₂


def trit_add(a, b):
    return (a + b) % MOD3


def trit_neg(a):
    return (MOD3 - a) % MOD3


# AlphaPower: ⟨α⟩ ≅ C₄, 下标相加 mod 4
ALPHA = (0, 1, 2, 3)  # a0, a1, a2, a3


def alpha_mul(a, b):
    return (a + b) % MOD4


def alpha_inv(a):
    return (MOD4 - a) % MOD4


# DuodecPoint = Trit × AlphaPower
DC_POINTS = tuple(itertools.product(TRIT, ALPHA))


def mixed_op(p, q):
    """Agda: mixedOp (x,a) (y,b) = (x ⊕ y, mulAlpha a b)"""
    return (trit_add(p[0], q[0]), alpha_mul(p[1], q[1]))


def duodec_e():
    return (0, 0)  # (T₀, a0)


def duodec_inv(p):
    """Agda: duodec-inv (x,a) = (negate x, alphaInv a)"""
    return (trit_neg(p[0]), alpha_inv(p[1]))


def sigma_dc(p):
    """Agda: sigmaDC (t,a) = (t, alphaInv a)

    Frobenius σ(x) = x³ 在 ⟨α⟩ 上诱导 α ↦ α³ = α⁻¹（因 α⁴ = 1）。
    注意: 幅度分量 t 不动，只对相位分量取逆 —— 相位不可约，不得约化为 {±1}。
    """
    return (p[0], alpha_inv(p[1]))


# Duodec = Z/12Z (投影层)
DUODEC = tuple(range(MOD12))


def plus12(x, y):
    return (x + y) % MOD12


def pi4(x):
    """Agda: π4 : Duodec → Fin 4 (mod 4)"""
    return x % MOD4


def fin4_suc(i):
    return (i + 1) % MOD4


def plus4(i, j):
    return (i + j) % MOD4


# ------------------------------------------------------------
# §2. 与 Agda 定理对应的交叉验证
# ------------------------------------------------------------


class TestPi4Homomorphism(unittest.TestCase):
    """对应 Agda: Sovereign.Algebra.Pi4Homomorphism.pi4-homo-+"""

    def test_homomorphism_all_144(self):
        """∀ x y → π4 (x +12 y) ≡ π4 x +4 π4 y —— 144 对全域穷举"""
        bad = [
            (x, y) for x, y in itertools.product(DUODEC, DUODEC)
            if pi4(plus12(x, y)) != plus4(pi4(x), pi4(y))
        ]
        self.assertEqual(bad, [], f"反例: {bad}")

    def test_plus1_commutes(self):
        """对应 Agda: pi4-+1 —— π4 (+1 x) ≡ fin4-suc (π4 x)"""
        for x in DUODEC:
            self.assertEqual(pi4((x + 1) % MOD12), fin4_suc(pi4(x)))

    def test_fin4_period(self):
        """对应 Agda: fin4-suc-4 —— 迭代 4 步 = 恒等"""
        for i in range(MOD4):
            v = i
            for _ in range(4):
                v = fin4_suc(v)
            self.assertEqual(v, i)


class TestDuodecPointGroup(unittest.TestCase):
    """对应 Agda: DuodecClock / DCGroup"""

    def test_assoc(self):
        for p, q, r in itertools.product(DC_POINTS, repeat=3):
            self.assertEqual(mixed_op(mixed_op(p, q), r), mixed_op(p, mixed_op(q, r)))

    def test_comm(self):
        for p, q in itertools.product(DC_POINTS, repeat=2):
            self.assertEqual(mixed_op(p, q), mixed_op(q, p))

    def test_identity(self):
        e = duodec_e()
        for p in DC_POINTS:
            self.assertEqual(mixed_op(e, p), p)
            self.assertEqual(mixed_op(p, e), p)

    def test_inverse(self):
        e = duodec_e()
        for p in DC_POINTS:
            self.assertEqual(mixed_op(p, duodec_inv(p)), e)
            self.assertEqual(mixed_op(duodec_inv(p), p), e)

    def test_inv_involutive(self):
        """对应 Agda: DCInvolution.duodec-inv-involutive"""
        for p in DC_POINTS:
            self.assertEqual(duodec_inv(duodec_inv(p)), p)

    def test_joint_period_12(self):
        """对应 Agda: mixedOp-12-cycle —— 联合生成元 g=(T₁,a1) 走 12 步回原点"""
        g = (1, 1)  # (T₁, a1)
        for p in DC_POINTS:
            v = p
            for _ in range(12):
                v = mixed_op(g, v)
            self.assertEqual(v, p)


class TestSigmaDCAutomorphism(unittest.TestCase):
    """对应 Agda: Sovereign.Algebra.GroupTheory.DCSigmaAut

    σ_DC 是 DC 的群自同构: 乘性 + 单位保持 + 逆元保持（+ 对合，见 DCGroup）。
    """

    def test_sigma_homomorphism_all_144(self):
        """∀ p q → σ(mixedOp p q) ≡ mixedOp (σ p) (σ q) —— 144 对全域穷举"""
        bad = [
            (p, q) for p, q in itertools.product(DC_POINTS, repeat=2)
            if sigma_dc(mixed_op(p, q)) != mixed_op(sigma_dc(p), sigma_dc(q))
        ]
        self.assertEqual(bad, [], f"反例: {bad}")

    def test_sigma_fixes_identity(self):
        """σ duodec-e ≡ duodec-e"""
        self.assertEqual(sigma_dc(duodec_e()), duodec_e())

    def test_sigma_preserves_inverse(self):
        """∀ p → σ(duodec-inv p) ≡ duodec-inv (σ p)"""
        for p in DC_POINTS:
            self.assertEqual(sigma_dc(duodec_inv(p)), duodec_inv(sigma_dc(p)))

    def test_sigma_involution(self):
        """对应 Agda: DCGroup.sigmaDC-involution —— σ² = id"""
        for p in DC_POINTS:
            self.assertEqual(sigma_dc(sigma_dc(p)), p)

    def test_sigma_fixes_amplitude_component(self):
        """幅度分量不动: σ 只作用于相位 C₄（相位不可约性元公理）"""
        for p in DC_POINTS:
            self.assertEqual(sigma_dc(p)[0], p[0])

    def test_sigma_is_nontrivial_bijection(self):
        """σ 是 12 点上非平凡双射（自同构不是恒等映射）"""
        img = {sigma_dc(p) for p in DC_POINTS}
        self.assertEqual(len(img), len(DC_POINTS))  # 单射 ⟹ 双射
        self.assertTrue(any(sigma_dc(p) != p for p in DC_POINTS))  # 非平凡


class TestNoInformationTruncation(unittest.TestCase):
    """无信息截断要求：载体必须保留两个分量；有损投影必须被识别为非单射"""

    def test_carrier_is_full_product(self):
        self.assertEqual(len(DC_POINTS), 12)
        self.assertEqual(len(set(DC_POINTS)), 12)

    def test_amplitude_only_projection_is_lossy(self):
        """只保留幅度 (trit) 的投影：12 → 3，非单射 = 相位信息丢失"""
        img = {p[0] for p in DC_POINTS}
        self.assertEqual(len(img), 3)
        self.assertLess(len(img), len(DC_POINTS))

    def test_c4_to_c2_projection_is_lossy(self):
        """相位 C₄ → C₂ 非忠实商 (相位不可约性元公理)：4 → 2，非单射"""
        img = {p[1] % 2 for p in DC_POINTS}
        self.assertEqual(len(img), 2)
        # 90° 与 270° 被压成同一值 —— 结构性语义错配
        self.assertEqual(1 % 2, 3 % 2)

    def test_phase_fiber_is_three(self):
        """每个相位值上恰好 3 个幅度值（纤维结构 GF(3) 为底、C₄ 为纤维）"""
        for a in ALPHA:
            fiber = [p for p in DC_POINTS if p[1] == a]
            self.assertEqual(len(fiber), 3)

    def test_no_float_in_this_model(self):
        """禁浮点：本文件全整数；此处断言所有模型输出为 int"""
        for p in DC_POINTS:
            self.assertIsInstance(p[0], int)
            self.assertIsInstance(p[1], int)
            q = sigma_dc(p)
            self.assertIsInstance(q[0], int)
            self.assertIsInstance(q[1], int)


if __name__ == "__main__":
    unittest.main(verbosity=2)
