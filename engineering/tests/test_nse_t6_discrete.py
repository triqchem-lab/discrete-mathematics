"""
T⁶ = (Z/3)⁶ 离散 Navier-Stokes 断言核对：Python 精确整数**对抗验证器**
====================================================================
方法论：先算后验证（zcode 提议，本项目双轨制的形式化）
  · Python 侧：精确整数穷举 / 找反例 —— 这是**证据**，不是证明
  · Agda 侧：唯一裁决器。本文件镜像的权威定义来自
      src/Sovereign/Problem/NavierStokes/NSEOnT6.agda
        §1 载体 Torus6 = C3⁶（729 点）, Field = 6 个标量场
        §2 diffF i f x = f(x+e_i) ⊕ negate(f(x))          (前向差分 D_i = S_i - I)
           div v x = sum6 (D₀v₁) (D₁v₂) (D₂v₃) (D₀v₄) (D₁v₅) (D₂v₆)
           axisLap i f = diffF i (diffF i f),  laplacian = 2·Σ_{i<3} axisLap i
           grad f = (D₀f, D₁f, D₂f, D₀f, D₁f, D₂f)          (六分量复用三轴)
        §5 div-grad : div (grad f) x ≡ laplacian f x          (refl)
        §6 nsStep v = leray v +F grad (div v)  (leray = id)
  · 无信息截断：载体 6 分量、三轴移位表、右嵌套 sum6 全部逐行镜像，
    不把 6 分量压成 3 分量，不把 T⁶ 压成 T³。

本文件的定位（务必先读）：
  它是**对抗验证器**，不是「断言通过器」。A1–A5 的原始陈述经 729 点精确穷举
  **被否证**（并给出精确反例），因此对应测试断言的是**反例的存在与精确取值**：
  若将来有人改动算子定义使原始陈述变真，这些测试会**失败并报警**。
  同时每个断言旁给出**特征 3 下真正成立的替代命题**（D³ ≡ 0 等），
  它们是 Agda 侧应当形式化的正确目标。

断言状态总表（详见各 TestCase 的 docstring）：
  A1  lap(f) ≡ 0                      否证   反例: laplacian(δ₀)(e₀) = 2
  A2  div(grad(div v)) ≡ 0            否证   等价于 A1（div-grad = laplacian）
  A3  不可压保持                       分裂   父口径 nsStep 否证; Agda 口径成立
  A4  div(adv v) ≡ -v                 否证   类型不合法 + 分量口径反例
  A5  D_i²f(x) = f(x+2e_i)+f(x)        否证   真命题为三点循环和
  A6  3⁶·3⁷²⁹ = 3⁷³⁵                   成立

零外部依赖；全整数精确运算；禁浮点（宪法约束）。
"""

import itertools
import random
import unittest

# ------------------------------------------------------------
# §1. 载体：T⁶ = (Z/3)⁶
# ------------------------------------------------------------

P = 3                      # 特征 3
AXES = 3                   # 移位轴数（Agda shiftAt 只区分 3 个轴）
DIM = 6                    # 场分量数 / 坐标维数
N_POINTS = P ** DIM        # 729

POINTS = tuple(itertools.product(range(P), repeat=DIM))
IDX = {x: k for k, x in enumerate(POINTS)}
ORIGIN = (0,) * DIM


def shift_point(axis, x):
    """Agda shiftAt：沿第 axis 轴 +1 (mod 3)，其余坐标不动。"""
    y = list(x)
    y[axis] = (y[axis] + 1) % P
    return tuple(y)


# 逐轴移位索引表（NBR[axis][k] = POINTS[k] 沿 axis 移位后的点下标）
NBR = tuple(tuple(IDX[shift_point(i, x)] for x in POINTS) for i in range(AXES))

# 分量 → 轴 的复用表（Agda div/grad：分量 0..5 用轴 0,1,2,0,1,2）
AXIS_OF = tuple(j % AXES for j in range(DIM))


# ------------------------------------------------------------
# §2. 算子镜像（与 NSEOnT6.agda §2/§5/§6 逐行对应）
#
# 标量场 = 长度 729 的 int 元组；向量场 = 6 个标量场的元组。
# 全部运算模 3，全程整数。
# ------------------------------------------------------------

def shift_field(axis, f):
    """shiftF i f x = f (shiftAt i x)"""
    nb = NBR[axis]
    return tuple(f[nb[k]] for k in range(N_POINTS))


def diff_field(axis, f):
    """diffF i f x = shiftF i f x ⊕ negate (f x)"""
    s = shift_field(axis, f)
    return tuple((s[k] - f[k]) % P for k in range(N_POINTS))


def sum6_right_nested(a, b, c, d, e, g):
    """Agda sum6 的右嵌套逐点镜像：a ⊕ (b ⊕ (c ⊕ (d ⊕ (e ⊕ (g ⊕ T₀)))))"""
    out = []
    for k in range(N_POINTS):
        t = (g[k] + 0) % P
        t = (e[k] + t) % P
        t = (d[k] + t) % P
        t = (c[k] + t) % P
        t = (b[k] + t) % P
        t = (a[k] + t) % P
        out.append(t)
    return tuple(out)


def sum_flat(fs):
    """平坦模 3 求和（与右嵌套等价的对照实现）"""
    acc = [0] * N_POINTS
    for f in fs:
        for k in range(N_POINTS):
            acc[k] = (acc[k] + f[k]) % P
    return tuple(acc)


def div(v):
    """div v x = Σ_j diffF (AXIS_OF j) (v_j) x"""
    return sum6_right_nested(
        diff_field(AXIS_OF[0], v[0]), diff_field(AXIS_OF[1], v[1]),
        diff_field(AXIS_OF[2], v[2]), diff_field(AXIS_OF[3], v[3]),
        diff_field(AXIS_OF[4], v[4]), diff_field(AXIS_OF[5], v[5]))


def grad(f):
    """grad f = (D₀f, D₁f, D₂f, D₀f, D₁f, D₂f)"""
    return tuple(diff_field(AXIS_OF[j], f) for j in range(DIM))


def axis_lap(axis, f):
    """axisLap i f = diffF i (diffF i f)"""
    return diff_field(axis, diff_field(axis, f))


def laplacian(f):
    """laplacian f = sum6 (axisLap 0) (axisLap 1) (axisLap 2) (axisLap 0) (axisLap 1) (axisLap 2)"""
    return sum6_right_nested(
        axis_lap(0, f), axis_lap(1, f), axis_lap(2, f),
        axis_lap(0, f), axis_lap(1, f), axis_lap(2, f))


def add_fields(u, w):
    return tuple(tuple((u[i][k] + w[i][k]) % P for k in range(N_POINTS))
                 for i in range(DIM))


def neg_field(f):
    return tuple((-t) % P for t in f)


def adv(v):
    """adv_i = Σ_j v_j ⊗ D_j v_i  (对流项 (v·∇)v，分量 i)

    注：Agda NSEOnT6 尚未定义 adv / nsStep(adv) 版本；本函数按父任务口径
    `adv_i = Σ_j v_j * D_j v_i` 实现，轴复用表与 div/grad 一致（AXIS_OF）。
    """
    out = []
    for i in range(DIM):
        terms = []
        for j in range(DIM):
            dj = diff_field(AXIS_OF[j], v[i])
            terms.append(tuple((v[j][k] * dj[k]) % P for k in range(N_POINTS)))
        out.append(sum6_right_nested(*terms))
    return tuple(out)


def leray(v):
    """Agda leray v = v（压力 Poisson 无约束 → Leray 投影 = id）"""
    return v


def ns_step_agda(v):
    """Agda nsStep v = leray v +F grad (div v)"""
    return add_fields(leray(v), grad(div(v)))


def ns_step_parent(v):
    """父任务口径 nsStep v = v + grad (div (adv v))"""
    return add_fields(v, grad(div(adv(v))))


def field_is_zero(f):
    return all(t == 0 for t in f)


# ------------------------------------------------------------
# §3. 场族（结构化 + 随机种子）
# ------------------------------------------------------------

def const_field(c):
    return tuple(c for _ in range(N_POINTS))


def coord_field(k):
    return tuple(x[k] for x in POINTS)


def delta_field(center):
    return tuple(1 if x == center else 0 for x in POINTS)


def structured_scalar_fields():
    """结构化标量场族：零场 / 坐标 / 常数 / 平方 / 两两乘积 / δ 指示"""
    fs = [const_field(0), const_field(1), const_field(2)]
    fs += [coord_field(k) for k in range(DIM)]
    fs += [tuple((x[k] * x[k]) % P for x in POINTS) for k in range(DIM)]
    fs += [tuple((x[k] * x[l]) % P for x in POINTS)
           for k in range(DIM) for l in range(k + 1, DIM)]
    centers = [ORIGIN, shift_point(0, ORIGIN), shift_point(0, shift_point(0, ORIGIN)),
               (0, 0, 0, 1, 0, 0), (1, 2, 0, 1, 2, 0), (2, 2, 2, 2, 2, 2)]
    fs += [delta_field(c) for c in centers]
    return fs


def random_scalar_fields(n, seed0):
    """可复现随机标量场族（每场独立种子）"""
    out = []
    for s in range(n):
        r = random.Random(seed0 + s)
        out.append(tuple(r.randrange(P) for _ in range(N_POINTS)))
    return out


_CACHE = {}


def scalar_family():
    if "scalar" not in _CACHE:
        _CACHE["scalar"] = structured_scalar_fields() + random_scalar_fields(12, 20260909)
    return _CACHE["scalar"]


def random_vector_fields(n, seed0):
    out = []
    for s in range(n):
        out.append(tuple(random_scalar_fields(1, seed0 + 100 * s + j)[0]
                         for j in range(DIM)))
    return out


def structured_vector_fields():
    """结构化向量场族：6 个单位常向量 + 坐标场向量 + δ 向量"""
    fs = []
    for j in range(DIM):
        fs.append(tuple(const_field(1) if i == j else const_field(0)
                        for i in range(DIM)))
    fs.append(tuple(coord_field(k) for k in range(DIM)))
    fs.append(tuple(delta_field(ORIGIN) for _ in range(DIM)))
    fs.append(tuple(delta_field(shift_point(1, ORIGIN)) for _ in range(DIM)))
    return fs


def vector_family():
    if "vector" not in _CACHE:
        _CACHE["vector"] = structured_vector_fields() + random_vector_fields(12, 31415926)
    return _CACHE["vector"]


def incompressible_from_potentials(p0, p1, p2):
    """势构造的无散度场（精确可验证）：

      (v₀,v₁) = (D₁ψ₀, -D₀ψ₀)  ⟹  D₀v₀ + D₁v₁ = D₀D₁ψ₀ - D₁D₀ψ₀ = 0
      (v₂,v₃) = (D₀ψ₁, -D₂ψ₁)  ⟹  D₂v₂ + D₀v₃ = 0
      (v₄,v₅) = (D₂ψ₂, -D₁ψ₂)  ⟹  D₁v₄ + D₂v₅ = 0
    不同轴差分可交换 ⟹ div v ≡ 0（逐点精确）。
    """
    d1p0 = diff_field(1, p0)
    d0p0 = diff_field(0, p0)
    d0p1 = diff_field(0, p1)
    d2p1 = diff_field(2, p1)
    d2p2 = diff_field(2, p2)
    d1p2 = diff_field(1, p2)
    return (d1p0, neg_field(d0p0), d0p1, neg_field(d2p1), d2p2, neg_field(d1p2))


def incompressible_family(n=40, seed0=11000):
    """n 个随机势生成的无散度场（div v ≡ 0 已在测试中精确核对）"""
    key = "inc%d" % n
    if key not in _CACHE:
        _CACHE[key] = [incompressible_from_potentials(
            random_scalar_fields(1, seed0 + 3 * s + 0)[0],
            random_scalar_fields(1, seed0 + 3 * s + 1)[0],
            random_scalar_fields(1, seed0 + 3 * s + 2)[0]) for s in range(n)]
    return _CACHE[key]


# 样本量常量（供报告与回归对照）
N_SCALAR = len(scalar_family())
N_VECTOR = len(vector_family())
N_INCOMP = 40


# ------------------------------------------------------------
# §4. A6 —— 状态空间计数（唯一成立的原始断言）
# ------------------------------------------------------------

class TestA6StateSpaceCount(unittest.TestCase):
    """A6: |State| = |T⁶| · |Field| = 3⁶ · 3⁷²⁹ = 3⁷³⁵（Agda NSEOnT6 §7）"""

    def test_A6_exponent_identity(self):
        self.assertEqual(3 ** 6 * 3 ** 729, 3 ** 735)

    def test_A6_grid_and_field_sizes(self):
        self.assertEqual(N_POINTS, 3 ** 6)
        self.assertEqual(N_POINTS, 729)
        self.assertEqual(len(POINTS), N_POINTS)
        self.assertEqual(len(set(POINTS)), N_POINTS)

    def test_A6_state_space_is_finite_huge(self):
        """有限但巨大：鸽巢原理可用（无有限时间爆破的结构前提）"""
        state = 3 ** 6 * 3 ** 729
        self.assertEqual(state, 3 ** 735)
        self.assertGreater(state, 0)
        self.assertIsInstance(state, int)


# ------------------------------------------------------------
# §5. A1 —— lap(f) ≡ 0：**否证**
# ------------------------------------------------------------

class TestA1LapVanishesRefuted(unittest.TestCase):
    """A1 原始陈述「∀ f ∀ x, lap(f)(x) == 0」被否证。

    真相（特征 3）：D_i = S_i - I 满足 (S_i - I)³ = S_i³ - I = 0（S_i³ = id），
    故 **三阶差分恒零** D_i³ ≡ 0；但二阶差分
        D_i²f(x) = f(x) + f(x+e_i) + f(x+2e_i)   （三点循环和，模 3）
    一般非零，所以 laplacian = 2·Σ_{i<3} D_i² 一般非零。
    最小反例：f = δ₀（原点指示场），x = e₀（坐标 0 取 1）处 lap = 2。
    """

    def test_A1_stated_claim_refuted_by_delta_witness(self):
        f = delta_field(ORIGIN)
        lap = laplacian(f)
        e0 = shift_point(0, ORIGIN)
        self.assertEqual(lap[IDX[e0]], 2)
        self.assertNotEqual(lap[IDX[e0]], 0)

    def test_A1_nonzero_set_is_exactly_six_axis_points(self):
        """δ₀ 的非零点恰为 {e₀,2e₀,e₁,2e₁,e₂,2e₂}，值全为 2"""
        f = delta_field(ORIGIN)
        lap = laplacian(f)
        expected = {}
        for axis in range(AXES):
            for t in (1, 2):
                x = list(ORIGIN)
                x[axis] = t
                expected[tuple(x)] = 2
        nz = {x: lap[IDX[x]] for x in POINTS if lap[IDX[x]] != 0}
        self.assertEqual(nz, expected)

    def test_A1_counterexample_count_over_families(self):
        """样本内反例计数 (场, 点) 对（样本量见 docstring 常量）"""
        total = 0
        for f in scalar_family():
            lap = laplacian(f)
            total += sum(1 for k in range(N_POINTS) if lap[k] != 0)
        self.assertGreater(total, 0)

    def test_A1_module_hypothesis_lap0_is_false(self):
        """NSEOnT6 把不可压保持陈述为 `(∀ f x → laplacian f x ≡ T₀) → ...`，
        该假设本身为假 —— 故条件形式的证明义务不可满足（Agda 侧 line 406 报错）。"""
        lap0_holds = all(laplacian(f)[k] == 0
                         for f in scalar_family() for k in range(N_POINTS))
        self.assertFalse(lap0_holds)

    def test_A1_correct_replacement_D3_vanishes(self):
        """**真命题**（Agda 应证目标）：∀ f x i, D_i³ f(x) ≡ 0"""
        for f in scalar_family():
            for i in range(AXES):
                d3 = diff_field(i, diff_field(i, diff_field(i, f)))
                self.assertTrue(field_is_zero(d3),
                                "D_i³ ≠ 0 (轴 %d)" % i)

    def test_A1_correct_replacement_cycle_sum(self):
        """**真命题**：D_i²f(x) = f(x) + f(x+e_i) + f(x+2e_i) (mod 3)"""
        for f in scalar_family():
            for i in range(AXES):
                lhs = axis_lap(i, f)
                for k, x in enumerate(POINTS):
                    rhs = (f[k] + f[NBR[i][k]] + f[NBR[i][NBR[i][k]]]) % P
                    self.assertEqual(lhs[k], rhs)

    def test_A1_correct_replacement_axis_lap_squared_zero(self):
        """**真命题**：(D_i²)² = 0（单轴二阶差分的平方为零；lap² ≠ 0，勿混）"""
        for f in scalar_family():
            for i in range(AXES):
                self.assertTrue(field_is_zero(axis_lap(i, axis_lap(i, f))))

    def test_A1_laplacian_is_twice_axis_sum(self):
        """laplacian = 2·Σ_{i<3} D_i²（Agda sum6 的轴复用），逐点核对"""
        for f in scalar_family():
            lap = laplacian(f)
            for k in range(N_POINTS):
                s = (axis_lap(0, f)[k] + axis_lap(1, f)[k] + axis_lap(2, f)[k]) % P
                self.assertEqual(lap[k], (2 * s) % P)

    def test_A1_sum6_right_nested_equals_flat(self):
        """Agda sum6 右嵌套与平坦模 3 求和等价（右嵌套只是定义形状）"""
        fs = scalar_family()[:6]
        self.assertEqual(sum6_right_nested(*fs[:6]), sum_flat(fs[:6]))


# ------------------------------------------------------------
# §6. A2 —— div(grad(div v)) ≡ 0：**否证**
# ------------------------------------------------------------

class TestA2DivGradDivRefuted(unittest.TestCase):
    """A2 原始陈述被否证：Agda §5 `div-grad : div (grad f) x ≡ laplacian f x`（refl），
    所以 A2 与 A1 是同一条命题 —— A1 假则 A2 假。"""

    def test_A2_identity_div_grad_equals_laplacian(self):
        """div (grad f) ≡ laplacian f（Agda 定义为 refl，此处逐点核对）"""
        for f in scalar_family():
            self.assertEqual(div(grad(f)), laplacian(f))

    def test_A2_stated_claim_refuted_witness(self):
        """在向量场族中搜索 div(grad(div v)) 非零的反例"""
        witness = None
        for v2 in vector_family():
            g = div(grad(div(v2)))
            for k in range(N_POINTS):
                if g[k] != 0:
                    witness = (v2, POINTS[k], g[k])
                    break
            if witness:
                break
        self.assertIsNotNone(witness, "样本内未找到反例（不应发生）")
        self.assertNotEqual(witness[2], 0)

    def test_A2_counterexample_count_over_families(self):
        total = 0
        for v in vector_family():
            g = div(grad(div(v)))
            total += sum(1 for k in range(N_POINTS) if g[k] != 0)
        self.assertGreater(total, 0)

    def test_A2_explicit_polynomial_witness(self):
        """确定性反例：v₀ = x₀·x₁，其余分量 0 —— lap(div v) 在原点非零"""
        v = (tuple((x[0] * x[1]) % P for x in POINTS),
             const_field(0), const_field(0),
             const_field(0), const_field(0), const_field(0))
        g = div(grad(div(v)))
        self.assertNotEqual(g[IDX[ORIGIN]], 0)


# ------------------------------------------------------------
# §7. A3 —— 不可压保持：父口径**否证** / Agda 口径**成立**
# ------------------------------------------------------------

class TestA3IncompressibilityPreservation(unittest.TestCase):
    """A3 分裂为两条命题：

    (a) Agda 口径 nsStep v = v + grad(div v)：若 div v ≡ 0 则 div(nsStep v) ≡ 0
        —— **成立**（div v 逐点为 0 ⟹ grad(div v) 为零场 ⟹ nsStep v = v）。
        这是 NSEOnT6 §6 的真实内容（其证明虽写成条件形式，结论无条件成立）。
    (b) 父任务口径 nsStep v = v + grad(div(adv v))：**否证**，因为
        div(nsStep v) = div v ⊕ lap(div(adv v))，第二项一般非零。
    """

    def test_A3_incompressible_construction_is_valid(self):
        """势构造的 40 个场逐点精确无散度"""
        for v in incompressible_family(N_INCOMP):
            self.assertTrue(field_is_zero(div(v)))

    def test_A3_agda_nsstep_preserves_incompressible(self):
        """Agda 口径：0 反例（40 个无散度场 × 729 点）"""
        bad = 0
        for v in incompressible_family(N_INCOMP):
            d = div(ns_step_agda(v))
            bad += sum(1 for k in range(N_POINTS) if d[k] != 0)
        self.assertEqual(bad, 0)

    def test_A3_agda_nsstep_equals_v_for_incompressible(self):
        """无散度时 grad(div v) 为零场 ⟹ nsStep v ≡ v（逐点逐分量）"""
        for v in incompressible_family(N_INCOMP):
            self.assertEqual(ns_step_agda(v), v)

    def test_A3_parent_nsstep_refuted(self):
        """父口径：反例存在（lap(div(adv v)) 非零）"""
        bad = 0
        for v in incompressible_family(N_INCOMP):
            d = div(ns_step_parent(v))
            bad += sum(1 for k in range(N_POINTS) if d[k] != 0)
        self.assertGreater(bad, 0)

    def test_A3_parent_nsstep_explicit_witness(self):
        """确定性反例：势 ψ₀ = x₀·x₁, ψ₁ = 0, ψ₂ = x₁·x₂ 时原点处 div(nsStep) ≠ 0"""
        p0 = tuple((x[0] * x[1]) % P for x in POINTS)
        p1 = const_field(0)
        p2 = tuple((x[1] * x[2]) % P for x in POINTS)
        v = incompressible_from_potentials(p0, p1, p2)
        self.assertTrue(field_is_zero(div(v)))          # 前提：不可压
        d = div(ns_step_parent(v))
        self.assertNotEqual(d[IDX[ORIGIN]], 0)          # 结论：不保持

    def test_A3_adv_leibniz_identity(self):
        """对流项用到的乘积法则（真命题）：
        D_i(v_j·v_k)(x) = (D_i v_j)(x)·v_k(x) + v_j(x+e_i)·(D_i v_k)(x)"""
        for v in vector_family()[:8]:
            for j in range(DIM):
                for i in range(DIM):
                    aj = AXIS_OF[j]
                    lhs = diff_field(aj, tuple((v[j][k] * v[i][k]) % P
                                               for k in range(N_POINTS)))
                    dvj = diff_field(aj, v[j])
                    sfj = shift_field(aj, v[j])
                    dvi = diff_field(aj, v[i])
                    for k in range(N_POINTS):
                        rhs = (dvj[k] * v[i][k] + sfj[k] * dvi[k]) % P
                        self.assertEqual(lhs[k], rhs)


# ------------------------------------------------------------
# §8. A4 —— div(adv v) ≡ -v：**否证**（且类型不合法）
# ------------------------------------------------------------

class TestA4DivAdvRefuted(unittest.TestCase):
    """A4 有两处缺陷：

    ① 类型层面：div 的值域是**标量场**，-v 是**向量场**（6 分量），
       等式 `div(adv v) == -v` 不合法；且后续 `nsStep v == v + grad(-v)`
       中 grad 的定义域是标量场，`grad(-v)` 同样不合法（Agda 签名下无法书写）。
    ② 分量口径（把右端读作 -v_i，逐 i）：**否证**。
       最小反例：常向量场 v = (0,1,0,0,0,0)（div v ≡ 0），adv v ≡ 0
       ⟹ div(adv v) ≡ 0，而 -v₁ = 2 ≠ 0。
    一维对照：D(v·Dv) = -v 在 Z/3 的 27 个函数中**只有 v ≡ 0** 一个解。
    """

    def test_A4_constant_field_witness(self):
        v = tuple(const_field(c) for c in (0, 1, 0, 0, 0, 0))
        self.assertTrue(field_is_zero(div(v)))              # 无散度
        self.assertTrue(field_is_zero(div(adv(v))))         # div(adv v) ≡ 0
        self.assertEqual(div(adv(v))[IDX[ORIGIN]], 0)
        self.assertEqual((-v[1][IDX[ORIGIN]]) % P, 2)       # -v₁ = 2 ≠ 0

    def test_A4_componentwise_reading_refuted(self):
        """分量口径：∃ i, x 使 div(adv v)(x) ≠ -v_i(x)"""
        v = tuple(const_field(c) for c in (0, 1, 0, 0, 0, 0))
        d = div(adv(v))
        mismatches = [(k, i) for k in range(N_POINTS) for i in range(DIM)
                      if d[k] != (-v[i][k]) % P]
        self.assertEqual(len(mismatches), N_POINTS * DIM)   # 全部 729×6 处都不等

    def test_A4_counterexample_count_over_family(self):
        bad = 0
        for v in incompressible_family(N_INCOMP):
            d = div(adv(v))
            for k in range(N_POINTS):
                for i in range(DIM):
                    if d[k] != (-v[i][k]) % P:
                        bad += 1
        self.assertGreater(bad, 0)

    def test_A4_scalar_reading_div_adv_equals_neg_div_v_refuted(self):
        """标量口径（右端读作 -div v）：同样否证"""
        bad = 0
        for v in incompressible_family(N_INCOMP):
            d = div(adv(v))
            dv = div(v)
            for k in range(N_POINTS):
                if d[k] != (-dv[k]) % P:
                    bad += 1
        self.assertGreater(bad, 0)

    def test_A4_1d_only_trivial_solution(self):
        """一维穷举 27 个 v：D(v·Dv) = -v 仅有 v ≡ 0"""
        sols = []
        for vals in itertools.product(range(P), repeat=3):
            nb = [(k + 1) % P for k in range(3)]
            dv = [(vals[nb[k]] - vals[k]) % P for k in range(3)]
            a = [(vals[k] * dv[k]) % P for k in range(3)]
            da = [(a[nb[k]] - a[k]) % P for k in range(3)]
            if da == [(-t) % P for t in vals]:
                sols.append(vals)
        self.assertEqual(sols, [(0, 0, 0)])

    def test_A4_correct_replacement_leibniz_decomposition(self):
        """**真命题**（对流项散度的正确展开）：
        div(adv v)(x) = Σ_{i,j} [ (D_i v_j)(x)·(D_j v_i)(x+e_i) + v_j(x)·(D_i D_j v_i)(x) ]"""
        for v in vector_family()[:6]:
            a = div(adv(v))
            di_vj, dj_vi_sh, dd_vi = {}, {}, {}
            for i in range(DIM):
                for j in range(DIM):
                    ai, aj = AXIS_OF[i], AXIS_OF[j]
                    di_vj[(i, j)] = diff_field(ai, v[j])
                    dj_vi_sh[(i, j)] = shift_field(ai, diff_field(aj, v[i]))
                    dd_vi[(i, j)] = diff_field(ai, diff_field(aj, v[i]))
            acc = [0] * N_POINTS
            for i in range(DIM):
                for j in range(DIM):
                    t1 = di_vj[(i, j)]
                    t2 = dj_vi_sh[(i, j)]
                    t3 = dd_vi[(i, j)]
                    vj = v[j]
                    for k in range(N_POINTS):
                        acc[k] = (acc[k] + t1[k] * t2[k] + vj[k] * t3[k]) % P
            self.assertEqual(a, tuple(acc))


# ------------------------------------------------------------
# §9. A5 —— D_i²f(x) = f(x+2e_i) + f(x)：**否证**
# ------------------------------------------------------------

class TestA5SecondDifferenceRefuted(unittest.TestCase):
    """A5 原始陈述被否证：漏掉了中间项 f(x+e_i)。

    正确式（模 3）：D_i²f(x) = f(x) + f(x+e_i) + f(x+2e_i)。
    最小反例：f = δ₀，i = 0，x = 2e₀ ⟹ 左端 1，右端 f(e₀) + f(2e₀) = 0。
    （若把右端理解为 f(x+2e_i) + f(x) + f(x+e_i)，则陈述为真 —— 见真命题测试。）
    """

    def test_A5_stated_claim_refuted_witness(self):
        f = delta_field(ORIGIN)
        witnesses = []
        for i in range(AXES):
            for k, x in enumerate(POINTS):
                lhs = axis_lap(i, f)[k]
                rhs = (f[NBR[i][NBR[i][k]]] + f[k]) % P
                if lhs != rhs:
                    witnesses.append((i, x, lhs, rhs))
        # 恰 3 个反例：(0,2e₀,1,0) (1,2e₁,1,0) (2,2e₂,1,0)
        self.assertEqual(len(witnesses), 3)
        for i, x, lhs, rhs in witnesses:
            self.assertEqual(x, shift_point(i, shift_point(i, ORIGIN)))
            self.assertEqual((lhs, rhs), (1, 0))

    def test_A5_counterexample_count_over_families(self):
        bad = 0
        for f in scalar_family():
            for i in range(AXES):
                lhs = axis_lap(i, f)
                for k in range(N_POINTS):
                    if lhs[k] != (f[NBR[i][NBR[i][k]]] + f[k]) % P:
                        bad += 1
        self.assertGreater(bad, 0)

    def test_A5_correct_identity_includes_middle_term(self):
        """真命题：D_i²f(x) = f(x) + f(x+e_i) + f(x+2e_i)（中间项不可省）"""
        for f in scalar_family():
            for i in range(AXES):
                lhs = axis_lap(i, f)
                for k in range(N_POINTS):
                    rhs = (f[k] + f[NBR[i][k]] + f[NBR[i][NBR[i][k]]]) % P
                    self.assertEqual(lhs[k], rhs)


# ------------------------------------------------------------
# §10. 宪法合规：禁浮点 / 全整数
# ------------------------------------------------------------

class TestNoFloat(unittest.TestCase):
    def test_all_operator_outputs_are_int(self):
        f = scalar_family()[-1]
        v = vector_family()[-1]
        for t in laplacian(f):
            self.assertIsInstance(t, int)
        for comp in grad(f):
            for t in comp:
                self.assertIsInstance(t, int)
        for comp in adv(v):
            for t in comp:
                self.assertIsInstance(t, int)
        self.assertIsInstance(3 ** 6 * 3 ** 729, int)

    def test_all_values_inside_gf3(self):
        f = scalar_family()[-1]
        v = vector_family()[-1]
        for t in laplacian(f):
            self.assertIn(t, (0, 1, 2))
        for comp in adv(v):
            for t in comp:
                self.assertIn(t, (0, 1, 2))


if __name__ == "__main__":
    unittest.main(verbosity=2)
