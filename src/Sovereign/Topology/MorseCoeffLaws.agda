{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.MorseCoeffLaws
-- 任务书第五层·5.1 泛型化第三块：μ 乘积**一般组合律**
--
-- 数学背景：代数 Morse 边界的路由系数 μ(path) 是交替路径上系数的
--   乘积（GF(3)：Trit ⊗）。本模块闭合乘积的**一般组合律**：
--
--   ①单位律：μ ⊗ T₁ ≡ μ（T₁ 是乘法单位——恒等路由）
--   ②非零保持：μ ≢ T₀ ∧ ν ≢ T₀ ⟹ μ ⊗ ν ≢ T₀
--     （GF(3) 非零闭包——3×3 case，≤27 阈内）
--   ③ε 对消：T₂ ⊗ T₂ ≡ T₁（两次 V-箭头的符号对消——路径回退的
--     代数根据；2·2 = 4 ≡ 1）
--   ④组合两形态一致：cr-via 索引的两种括号
--     (μ_in ⊗ i) ⊗ (T₂ ⊗ ν) ≡ ((μ_in ⊗ i) ⊗ T₂) ⊗ ν
--     —— ⊗-assoc 直给（cr-via 索引与结合顺序无关）
--
--   ④是 Morse 复合**良定义性**的关键：无论把路径在哪一步切开，
--   总系数不变——泛型同调定理的系数层根据。
--
-- 复用：Base/Trit（⊗-identityʳ/⊗-comm/⊗-assoc 全 3-27 case 已证）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.MorseCoeffLaws where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; ⊗-assoc)

--------------------------------------------------------------------------------
-- §1. 单位律：μ ⊗ T₁ ≡ μ（恒等路由）
--------------------------------------------------------------------------------

unit-law : ∀ μ → μ ⊗ T₁ ≡ μ
unit-law T₀ = refl
unit-law T₁ = refl
unit-law T₂ = refl

--------------------------------------------------------------------------------
-- §2. 非零保持：GF(3) 非零系数闭包（3×3 case，≤27 阈内）
--------------------------------------------------------------------------------

-- 非零传播（GF(3) 非零闭包，3×3 = 9 case ≤27 阈内）
nn-keep : ∀ μ ν → ¬ (μ ≡ T₀) → ¬ (ν ≡ T₀) → ¬ (μ ⊗ ν ≡ T₀)
nn-keep T₁ T₁ hμ hν = λ ()
nn-keep T₁ T₂ hμ hν = λ ()
nn-keep T₂ T₁ hμ hν = λ ()
nn-keep T₂ T₂ hμ hν = λ ()
nn-keep T₀ ν hμ hν = ⊥-elim (hμ refl)
nn-keep T₁ T₀ hμ hν = ⊥-elim (hν refl)
nn-keep T₂ T₀ hμ hν = ⊥-elim (hν refl)

--------------------------------------------------------------------------------
-- §3. ε 对消：T₂ ⊗ T₂ ≡ T₁（两次 V-箭头符号对消）
--------------------------------------------------------------------------------

eps-cancel : T₂ ⊗ T₂ ≡ T₁
eps-cancel = refl

--------------------------------------------------------------------------------
-- §4. 组合两形态一致（cr-via 索引与括号顺序无关）
--
--   MorseCoeffRoute.cr-via 的索引写作 (μ_in ⊗ i) ⊗ (T₂ ⊗ ν)；
--   另一自然括号 ((μ_in ⊗ i) ⊗ T₂) ⊗ ν——⊗-assoc 直给等价。
--   这保证 cr-via 的总系数无论路径在哪一步"切开"都一致——
--   Morse 复合良定义性的系数层根据。
--------------------------------------------------------------------------------

assoc-form : ∀ μ-in i ν →
  ((μ-in ⊗ i) ⊗ (T₂ ⊗ ν)) ≡ (((μ-in ⊗ i) ⊗ T₂) ⊗ ν)
assoc-form μ-in i ν = sym (⊗-assoc (μ-in ⊗ i) T₂ ν)

-- 反向（右结合形态）
assoc-formʳ : ∀ μ-in i ν →
  (((μ-in ⊗ i) ⊗ T₂) ⊗ ν) ≡ ((μ-in ⊗ i) ⊗ (T₂ ⊗ ν))
assoc-formʳ μ-in i ν = sym (assoc-form μ-in i ν)
