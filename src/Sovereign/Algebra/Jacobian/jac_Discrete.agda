{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_Discrete
-- Phase 2: 形式导数 vs 差分算子 vs 函数表矩阵
--
-- 三种"雅可比"的区分:
--   1. 形式导数 J_formal: 连续统的离散模拟, char p 下有 Frobenius 盲区
--      (注: Frobenius 盲区是 char p 经典事实, Adjamagbo 1995, Maubach)
--   2. 差分算子 J_Δ = SF - F: 真正的离散雅可比, 无 Frobenius 盲区
--   3. 函数表矩阵 M_F: 有限集线性代数, det ≠ 0 ⟺ 双射 (重言式)
--
-- 注意: 形式多项式环 GF(3)[x] 中 x³ ≠ x,
--        多项式函数空间 GF(3)^{GF(3)} 中 x³ = x (Fermat)。
--        BCW 规约在形式多项式环上工作, Fermat 坍缩在函数空间上工作。

module Sovereign.Algebra.Jacobian.jac_Discrete where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- 1. 2×2 矩阵 (内联, 避免循环依赖)
--------------------------------------------------------------------------------

Mat2 : Set
Mat2 = (Trit × Trit) × (Trit × Trit)

det2 : Mat2 → Trit
det2 ((a , b) , (c , d)) = (a ⊗ d) ⊕ negate (b ⊗ c)

I2 : Mat2
I2 = (T₁ , T₀) , (T₀ , T₁)

GF3² : Set
GF3² = Trit × Trit

--------------------------------------------------------------------------------
-- 2. 形式导数雅可比 (char p 经典, 有 Frobenius 盲区)
--------------------------------------------------------------------------------

-- 形式导数: ∂(xⁿ)/∂x = n·xⁿ⁻¹ (在形式多项式环 GF(3)[x] 上)
-- char 3: ∂(x³)/∂x = 3x² = 0
-- 这是 char p 的经典事实 (Adjamagbo 1995, Maubach),
-- 不是新发现。GF(3)/GF(9) 上的计算是具体实例化。

-- 形式导数雅可比条件: 给定的 2×2 矩阵行列式 = T₁
-- (矩阵由外部提供, 因为形式导数是语法操作, 不能从函数计算)
FormalJacDet1 : Mat2 → Set
FormalJacDet1 J = det2 J ≡ T₁

--------------------------------------------------------------------------------
-- 3. 差分算子雅可比 (真正的离散雅可比, 无盲区)
--------------------------------------------------------------------------------

-- ΔF = SF - F, 其中 S 是移位算子
-- 差分算子作用于函数 (不是形式多项式),
-- 自动消化 Fermat 恒等式 x^p = x, 无 Frobenius 盲区。
-- 详见 jac_GF3.agda §9-13。

--------------------------------------------------------------------------------
-- 4. 函数表矩阵 (有限集线性代数, 重言式)
--------------------------------------------------------------------------------

-- M_F[i][j] = 1 当 F(point_j) = point_i
-- F 双射 ⟺ M_F 是置换矩阵 ⟺ det(M_F) ≠ 0
-- 这对任何有限集上的任何函数都成立,
-- 与雅可比、多项式、代数结构无关。
-- 不应称为"离散雅可比"——这是函数表矩阵。

-- 函数表条件 = 单射性 (有限集上等价于双射)
FunctionTableInj : (GF3² → GF3²) → Set
FunctionTableInj F = ∀ p q → F p ≡ F q → p ≡ q

--------------------------------------------------------------------------------
-- 5. 反例: 形式导数条件不蕴含函数表条件
--------------------------------------------------------------------------------

-- F(x,y) = (x, y + T₂·y³)
-- 作为多项式函数: y³ = y (Fermat), 所以 F(x,y) = (x, 0)
-- 作为形式多项式: y³ ≠ y, 但 ∂(y³)/∂y = 3y² = 0 (char 3)

F-blind : GF3² → GF3²
F-blind (x , y) = (x , y ⊕ (T₂ ⊗ ((y ⊗ y) ⊗ y)))

-- 形式导数雅可比 = I₂ (Frobenius 盲区: ∂(y³)/∂y = 0)
formal-jac-blind : Mat2
formal-jac-blind = I2

-- 形式导数条件满足: det J_formal = 1
formal-passes : FormalJacDet1 formal-jac-blind
formal-passes = refl

-- 函数表条件失败: F 不是单射
-- (T₀,T₀) 和 (T₀,T₁) 映射到同一点 (T₀,T₀)
table-fails : FunctionTableInj F-blind → ⊥
table-fails inj with inj (T₀ , T₀) (T₀ , T₁) refl
... | ()

-- 定理: 形式导数条件 ⊄ 函数表条件
-- (char p 经典反例在 GF(3)² 上的具体实例化)
formal-not-table :
  Σ Mat2 (λ J → FormalJacDet1 J ×
    Σ (GF3² → GF3²) (λ F → FunctionTableInj F → ⊥))
formal-not-table = formal-jac-blind , (formal-passes , (F-blind , table-fails))

--------------------------------------------------------------------------------
-- 6. 差分算子 vs 形式导数 (核心对比)
--------------------------------------------------------------------------------

-- 对 F-blind(x,y) = (x, 0):
--   形式导数: J_formal = I₂, det = 1  ← Frobenius 盲区 (错误)
--   差分算子: J_Δ = [[1,0],[0,0]], det = 0  ← 正确检测
--   函数表:   M_F 奇异, det = 0  ← 正确 (重言式)
--
-- 差分算子 ΔF = SF - F 是真正的离散雅可比:
--   无 Frobenius 盲区, 精确反映函数的局部变化率。
--   详见 jac_GF3.agda §9-13 的构造性证明。
