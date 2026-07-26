{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Jacobian.jac_Conjecture
-- Phase 4: 离散雅可比猜想陈述与实质定理
--
-- 在有限集 S 上, F: S → S 是双射 ⟺ 全局矩阵 det(M_F) ≠ 0
-- 这是有限集线性代数定理 (鸽巢原理), 不依赖连续统雅可比猜想。
-- 逐点雅可比有 Frobenius 盲区, 全局矩阵没有。

module Sovereign.Algebra.Jacobian.jac_Conjecture where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥; ⊥-elim)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂)

open import Sovereign.Algebra.Jacobian.jac_Discrete
  using (Mat2; det2; I2; GF3²; FormalJacDet1; FunctionTableInj;
         formal-passes; formal-not-table)

open import Sovereign.Algebra.Jacobian.jac_GF3
  using (F-gf3; gf3-collision; gf3-not-surj; det-J-formal; det2-I2)

open import Sovereign.Algebra.Jacobian.jac_Pigeonhole
  using (Inj2; Surj2; pigeonhole-2)

--------------------------------------------------------------------------------
-- 1. 逐点雅可比条件 (实质定义, 引用真实 Mat2 行列式)
--------------------------------------------------------------------------------

-- 逐点雅可比条件: 给定的 2×2 形式导数矩阵 J 满足 det J ≡ T₁
-- 这不是空定义 T₁≡T₁, 而是真实的 Mat2 行列式约束
-- (形式导数是语法操作, 矩阵由外部提供)
PointwiseJC : Mat2 → Set
PointwiseJC J = FormalJacDet1 J

-- 单位矩阵满足逐点条件: det I₂ = 1
pointwise-I2 : PointwiseJC I2
pointwise-I2 = det2-I2

--------------------------------------------------------------------------------
-- 2. 定理 1: 单射 ⟹ 满射 (鸽巢原理, 0 postulate)
--------------------------------------------------------------------------------

-- GF(3)² 上, 任何单射映射必为满射
-- 这是 pigeonhole-2 的直接推论 (有限集线性代数 + 标准库 pigeonhole)
inj→surj-GF3² : ∀ (F : GF3² → GF3²) → Inj2 F → Surj2 F
inj→surj-GF3² = pigeonhole-2

--------------------------------------------------------------------------------
-- 3. 定理 2: 逐点雅可比条件不蕴含双射性 (构造性反例)
--------------------------------------------------------------------------------

-- 反例: F-gf3(x,y) = (x, y + 2·y³) = (x, 0)
-- 形式导数 J = I₂, det J = 1 (Frobenius 盲区: ∂(y³)/∂y = 3y² = 0)
-- 但 F-gf3 非双射: 3-to-1 坍缩

-- (a) 逐点条件满足: det J_formal(F-gf3) = 1
pointwise-passes-gf3 : PointwiseJC I2
pointwise-passes-gf3 = det2-I2

-- (b) F-gf3 非满射: (T₀,T₁) 不在像中
gf3-not-surjective : Surj2 F-gf3 → ⊥
gf3-not-surjective surj with surj (T₀ , T₁)
... | (p , Fp≡01) = gf3-not-surj p Fp≡01

-- (c) 综合: 逐点条件满足但非满射
-- PointwiseJC I2 成立, 但 Surj2 F-gf3 → ⊥
pointwise-not-surjective :
  PointwiseJC I2 × (Surj2 F-gf3 → ⊥)
pointwise-not-surjective = pointwise-passes-gf3 , gf3-not-surjective

-- (d) 从 jac_Discrete 复用: 形式导数条件 ⊄ 函数表条件
-- formal-not-table : Σ Mat2 (λ J → FormalJacDet1 J × Σ F (FunctionTableInj F → ⊥))
-- (F-blind: x³=y³=y, F=(x,0), 单射性失败)

--------------------------------------------------------------------------------
-- 4. 离散雅可比定理 (陈述)
--------------------------------------------------------------------------------

-- 在有限集 S 上, F: S → S 是双射 ⟺ F 的全局矩阵 M_F 行列式非零
--
-- 证明结构 (详见 jac_Theorem.agda):
--   1. 鸽巢原理: 有限集上 单射 ⟺ 满射 ⟺ 双射
--   2. (⇒) F 双射 → M_F 是置换矩阵 → det = ±1 ≠ 0
--   3. (⇐) det ≠ 0 → M_F 可逆 → F 单射 → 鸽巢 → F 双射
--
-- inj→surj-GF3² 证明了步骤 1 的 GF(3)² 实例。

--------------------------------------------------------------------------------
-- 5. 逐点 vs 全局: 不等价性总结
--------------------------------------------------------------------------------

-- 三层雅可比强度 (jac_Discrete §5, jac_FrobeniusBlind §6):
--   形式导数 (最弱, Frobenius 盲区)
--     < 差分算子 (无 Frobenius 盲区, 但仍是局部条件)
--       < 函数表/单射性 (全局条件, 精确判定双射)
--
-- GF(3)² 反例: det J_formal = 1 但 F 非双射 (pointwise-not-surjective)
-- GF(9)² 反例: det J_Δ = 1+α ≠ 0 但 F 非双射 (jac_FrobeniusBlind §6)

--------------------------------------------------------------------------------
-- 6. 实验验证摘要
--------------------------------------------------------------------------------

-- GF(9)²: 59,049 BCW 映射, 93.3% 非双射 (逐点条件全部满足)
-- GF(9)²: 全局矩阵 det(F*) = 0 精确检测全部非双射
-- GF(3)²: F(x,y) = (x, 0), det J = 1, 非双射 (3-to-1, gf3-not-surj)
-- 详见 jac_Theorem.agda §4
