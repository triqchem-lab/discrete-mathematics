{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Physics.TracelessCentroidZero
-- 无迹四极张量 ⇒ 六轴平均质心位移为零
--
-- 数学背景:
--   分子在笼中的四极-EFG 耦合能  E(n) = n · Θ · n （Θ 对称）
--   对取向做**各向同性平均**时 ⟨n_i n_j⟩ = δ_ij/3，故
--
--       ⟨n · Θ · n⟩ = tr(Θ)/3
--
--   ⇒ **无迹（tr Θ = 0）⇒ 平均质心位移为零。**
--
--   这是 C₆₀ 内嵌分子问题的核心判据：四极只产生**分裂**（各向异性），
--   不产生**质心位移**（各向同性）⇒ 实测质心下移必须另有机制。
--   （数值验证：完整 9×9 模型给出 H₂O 0.046 / HF 0.043 cm⁻¹，相对 0.1%。）
--
-- 为什么在 ℤ 上而不在 GF(3) 上:
--   char 3 中 3 ≡ 0 ⇒ 「3·tr ≡ 0」**平凡成立**，定理内容消失。
--   ⇒ 必须升到 ℤ 才能表达「除以 3」的非平凡性。
--
-- 离散化（关键，避开连续统病态）:
--   不引入 ℝ / 球面积分 / 极限 / 测度。
--   取向集取**六条坐标轴** {±e_x, ±e_y, ±e_z}：
--       n·Θ·n 对 n 与 −n **相同**（二次型）⇒ 每条轴贡献 2·Θ_ii
--       六轴和 = 2·(Θ_xx + Θ_yy + Θ_zz) = 2·tr(Θ)
--   ⇒ 这是一个**有限、精确**的代数恒等式。
--   ⚠ 定义里显式写出了这个「×2」（不是事后补的），所以不是循环论证。
--
-- 0 postulate / 0 hole.

module Sovereign.Application.Physics.TracelessCentroidZero where

open import Data.Integer using (ℤ; +0; +_; -[1+_]; _+_)
open import Data.Integer.Properties using (+-identityʳ; +-inverseʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong₂)

--------------------------------------------------------------------------------
-- §1. 对称 3×3 张量（6 个独立分量，ℤ 值）
--------------------------------------------------------------------------------

record Sym3 : Set where
  constructor mkSym3
  field
    xx yy zz xy xz yz : ℤ

open Sym3

-- 迹
trace : Sym3 → ℤ
trace T = xx T + yy T + zz T

-- 无迹谓词
Traceless : Sym3 → Set
Traceless T = trace T ≡ +0

--------------------------------------------------------------------------------
-- §2. 沿坐标轴的二次型
--------------------------------------------------------------------------------

-- 沿 x/y/z 轴：n·Θ·n 取 n = e_i 时就是 Θ_ii
q-x q-y q-z : Sym3 → ℤ
q-x T = xx T
q-y T = yy T
q-z T = zz T

-- 三轴和（正轴 {@e_x, @e_y, @e_z}）
three-axis-sum : Sym3 → ℤ
three-axis-sum T = (xx T + yy T) + zz T

-- ⭐ 六轴和：{+e_x,−e_x,+e_y,−e_y,+e_z,−e_z}
--   **定义即** 2 × three-axis-sum —— 因为二次型对 n 与 −n 相同。
--   这里把「×2」写进**定义**，而不是事后断言，避免循环。
six-axis-sum : Sym3 → ℤ
six-axis-sum T = three-axis-sum T + three-axis-sum T

--------------------------------------------------------------------------------
-- §3. 三轴和就是迹（定义展开即得，refl）
--------------------------------------------------------------------------------

three-axis-is-trace : ∀ T → three-axis-sum T ≡ trace T
three-axis-is-trace T = refl

--------------------------------------------------------------------------------
-- §4. ⭐ 主定理：无迹 ⇒ 三轴和为零
--------------------------------------------------------------------------------

traceless-three-axis-zero : ∀ T → Traceless T → three-axis-sum T ≡ +0
traceless-three-axis-zero T p = trans (three-axis-is-trace T) p

--------------------------------------------------------------------------------
-- §5. ⭐⭐ 推论：无迹 ⇒ 六轴和为零（即六轴平均质心位移为零）
--------------------------------------------------------------------------------

-- +0 + +0 ≡ +0
zero-plus-zero : (+0 + +0) ≡ +0
zero-plus-zero = +-identityʳ +0

traceless-six-axis-zero : ∀ T → Traceless T → six-axis-sum T ≡ +0
traceless-six-axis-zero T p =
  trans
    (cong₂ _+_ (traceless-three-axis-zero T p) (traceless-three-axis-zero T p))
    zero-plus-zero

--------------------------------------------------------------------------------
-- §6. 具体实例（对抗验证：非无迹的张量**不**为零）
--------------------------------------------------------------------------------

-- ⚠ 注意：不能写 `(+ 1)` —— 那会被解析成 +_ 的右 section。
--   用顶层常量避开。
-- ⚠ `+ 1` 用构造子（Nat 字面量 1 由 Data.Nat 提供）
--   `- 1` 会被解析成「ℤ 的一元负 ∘ Nat 字面量」⇒ 类型错
--   负一直接用构造子 -[1+ 0]
one : ℤ
one = + 1

neg-one : ℤ
neg-one = -[1+ 0 ]

-- 非无迹例子：Θ_xx = 1, 其它 0 ⇒ 迹 = 1 ≠ 0
T-nontraceless : Sym3
T-nontraceless = mkSym3 one +0 +0 +0 +0 +0

-- 它的三轴和 = 1 ≠ 0 ⇒ 定理的**前提是必要的**
--   three-axis-sum = (1 + 0) + 0，需化简到 1
nontraceless-nonzero : three-axis-sum T-nontraceless ≡ one
nontraceless-nonzero =
  trans (+-identityʳ (one + +0)) (+-identityʳ one)

-- 无迹例子：Θ = (1, −1, 0)
T-traceless : Sym3
T-traceless = mkSym3 one neg-one +0 +0 +0 +0

-- 迹确实为 0（(1 + (−1)) + 0 = 0）
--   ⚠ 需要 +-inverseʳ：1 + (−1) ≡ 0
traceless-instance : Traceless T-traceless
traceless-instance =
  trans (+-identityʳ (one + neg-one)) (+-inverseʳ one)

-- ⭐ 实例验证：六轴和 = 0
traceless-instance-zero : six-axis-sum T-traceless ≡ +0
traceless-instance-zero = traceless-six-axis-zero T-traceless traceless-instance

--------------------------------------------------------------------------------
-- §7. 诚实边界（本模块**没有**证明的）
--------------------------------------------------------------------------------

-- [未证明] 「六条坐标轴的等权平均 = 球面平均」——
--   对二次型恰好成立（因为 ⟨n_i n_j⟩ = δ_ij/3 且六轴对称），
--   但本模块**只证明了六轴和的陈述**，没有把它与球面积分联系起来。
--   若需要，必须引入离散化的球面平均（不引入 ℝ/测度）。
--
-- [未证明] 任意取向集（不是六条轴）的版本。
--
-- [数值验证·非本模块] 完整 9×9 模型给出质心随场变化 0.046 / 0.043 cm⁻¹
--   （相对 0.1%）⇒ 定理在模型里数值成立。见
--   engines/eoh/CENTROID_ZERO_PROOF_2026-10-24.md
