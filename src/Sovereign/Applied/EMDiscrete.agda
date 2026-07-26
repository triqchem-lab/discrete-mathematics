{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Applied.EMDiscrete
-- C45: 离散电磁学 — Maxwell 截断 + 干涉
--
-- 核心命题:
--   1. Maxwell 截断: Δ³≡0 (三阶差分幂零 → 高阶 Maxwell 方程截断)
--   2. 干涉: T₁⊕T₂≡T₀ (GF(3) 相消干涉)
--
-- 0 postulate, 穷举法优先

module Sovereign.Applied.EMDiscrete where

open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Algebra.ProjectionDifferential
  using (GF3Func; Δ; Δ³≡0; Δ²-is-const; Δ-const-zero; sum3)

--------------------------------------------------------------------------------
-- §1. Maxwell 截断: Δ³ ≡ 0
--
-- 连续 Maxwell 方程: ∂F/∂x = J, 微分阶数不受限
-- 离散 Maxwell 方程: ΔF = J, 但 Δ³ ≡ 0 (幂零截断)
--
-- 物理意义: 离散电磁场的三阶及以上"导数"恒为零
-- 这是连续理论中不存在的截断——连续微分 d³/dx³ 不恒为零
--
-- 引用: Δ³≡0 (ProjectionDifferential.agda)
--------------------------------------------------------------------------------

-- Maxwell 截断: 三阶差分恒为零
maxwell-cutoff : ∀ (f : GF3Func) → Δ (Δ (Δ f)) ≡ (T₀ , T₀ , T₀)
maxwell-cutoff = Δ³≡0

-- 二阶差分坍缩为常数: Δ²f = (sum3(f), sum3(f), sum3(f))
maxwell-second-order : ∀ (f : GF3Func) → Δ (Δ f) ≡ (sum3 f , sum3 f , sum3 f)
maxwell-second-order = Δ²-is-const

-- 截断的数值验证: 4 阶也恒为零 (Δ⁴ = Δ∘Δ³ = Δ∘0 = 0)
maxwell-fourth-order : ∀ (f : GF3Func) → Δ (Δ (Δ (Δ f))) ≡ (T₀ , T₀ , T₀)
maxwell-fourth-order f = trans (cong Δ (Δ³≡0 f)) (Δ-const-zero T₀)

--------------------------------------------------------------------------------
-- §2. 干涉: GF(3) 相消/相长
--
-- 经典电磁干涉: E₁ + E₂ (实数叠加)
-- 离散干涉: T₁ ⊕ T₂ (GF(3) 叠加)
--
-- 相消干涉: T₁ ⊕ T₂ = T₀ (1 + 2 = 3 ≡ 0)
-- 相长干涉: T₁ ⊕ T₁ = T₂ (1 + 1 = 2, 增强)
-- 自干涉: T₂ ⊕ T₂ = T₁ (2 + 2 = 4 ≡ 1, 回绕)
--------------------------------------------------------------------------------

-- 相消干涉: T₁ ⊕ T₂ ≡ T₀
interference-destructive : T₁ ⊕ T₂ ≡ T₀
interference-destructive = refl

-- 相长干涉: T₁ ⊕ T₁ ≡ T₂
interference-constructive : T₁ ⊕ T₁ ≡ T₂
interference-constructive = refl

-- 回绕干涉: T₂ ⊕ T₂ ≡ T₁
interference-wraparound : T₂ ⊕ T₂ ≡ T₁
interference-wraparound = refl

-- 零干涉: T₀ ⊕ x ≡ x (真空不改变场)
interference-vacuum : ∀ (x : Trit) → T₀ ⊕ x ≡ x
interference-vacuum T₀ = refl
interference-vacuum T₁ = refl
interference-vacuum T₂ = refl

-- 干涉的特征 3: 三束同相光叠加归零
interference-char3 : ∀ (x : Trit) → (x ⊕ x) ⊕ x ≡ T₀
interference-char3 T₀ = refl
interference-char3 T₁ = refl
interference-char3 T₂ = refl

-- 手征共轭干涉: x ⊕ negate(x) ≡ T₀
interference-conjugate : ∀ (x : Trit) → x ⊕ negate x ≡ T₀
interference-conjugate T₀ = refl
interference-conjugate T₁ = refl
interference-conjugate T₂ = refl
