{-# OPTIONS --cubical --rewriting --guardedness #-}

-- | Sovereign.Topology.KerTrivial
-- 完备性层 C4：H₁ 核的无条件平凡化——∂₁ᶜ 单射的系数级展开（逐点版）
--
-- 数学内容：
--   K₃ 的 ∂₁ᶜ 逐点定义：
--     ∂₁ᶜ x fzero        = x fzero ⊗ T₁
--     ∂₁ᶜ x (fsuc fzero) = x fzero ⊗ T₂
--   核条件（两分量 ≡ T₀）经 ⊗-cancel（T₁/T₂ 非零消去）：
--     x fzero ≡ T₀ 逐点闭合——**无条件**（不需要 p ≡ 零点假设，
--     M7c 条件式版的升级）。
--
--   逐点纪律：本库无 funext——函数相等一律逐点陈述（∀ i → x i ≡ T₀
--   即核的逐点平凡）；Σ 完整点级的 PathP 组装留 roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.KerTrivial where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; trans; cong; sym)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Topology.MorseCriticalHomology using (∂₁ᶜ; C₀ᶜ; C₁ᶜ)
open import Sovereign.Algebra.FreeAb using (zeroᶠ)
open import Sovereign.Algebra.LiftCriterion
  using (NonZero₃; ⊗-cancel)

--------------------------------------------------------------------------------
-- §1. 核谓词——逐点两分量
--------------------------------------------------------------------------------

KerPt : C₁ᶜ → Set
KerPt x = (∂₁ᶜ x fzero ≡ T₀) × (∂₁ᶜ x (fsuc fzero) ≡ T₀)

--------------------------------------------------------------------------------
-- §2. C4 核心——核中系数逐点归零（无条件）
--------------------------------------------------------------------------------

-- T₁ 条件消去：x fzero ⊗ T₁ ≡ T₀ ⟹ x fzero ≡ T₀
ker-from-T₁ : ∀ (x : C₁ᶜ) → KerPt x → x fzero ≡ T₀
ker-from-T₁ x (h₁ , h₂) = ⊗-cancel (x fzero) T₀ T₁ tt h₁

-- T₂ 条件消去：x fzero ⊗ T₂ ≡ T₀ ⟹ x fzero ≡ T₀（冗余但独立成立）
ker-from-T₂ : ∀ (x : C₁ᶜ) → KerPt x → x fzero ≡ T₀
ker-from-T₂ x (h₁ , h₂) = ⊗-cancel (x fzero) T₀ T₂ tt h₂
-- 两条件冗余（任一即可）——∂₁ᶜ 单射的代数本质显式化

--------------------------------------------------------------------------------
-- §3. C4 无条件平凡——逐点形式
--
--   任意核中链 x，其唯一系数逐点归零：
--     KerPt x → ∀ (i : Fin 1) → x i ≡ T₀
--   Fin 1 只有 fzero——单分量全覆盖，完备（非抽样）。
--------------------------------------------------------------------------------

H₁-pt-trivial : ∀ (x : C₁ᶜ) → KerPt x → ∀ (i : Fin 1) → x i ≡ T₀
H₁-pt-trivial x kx fzero = ker-from-T₁ x kx
-- Fin 1 穷尽：唯一索引 fzero——逐点平凡即全平凡 ✓

-- 载体级（Σ 展开的逐点版）
H-carrier : Set
H-carrier = Σ C₁ᶜ KerPt

H-carrier-pt-trivial : ∀ (p : H-carrier) (i : Fin 1) → proj₁ p i ≡ T₀
H-carrier-pt-trivial (x , kx) i = H₁-pt-trivial x kx i

--------------------------------------------------------------------------------
-- §4. 零商对账——系数级（与 KerImQuot/ChainQuotIso 对账）
--------------------------------------------------------------------------------

open import Sovereign.Topology.ChainQuotIso using (Zero; zero-pt)

H₁→Zero : H-carrier → Zero
H₁→Zero p = zero-pt

Zero→H₁ : Zero → H-carrier
Zero→H₁ zero-pt = (zeroᶠ 1 , (refl , refl))
-- 零链的核谓词：∂₁ᶜ zeroᶠ 1 fzero = T₀⊗T₁ = T₀ ✓（refl 定义性）

-- 零点的逐点平凡（对账 KerImQuot.ker-zero）
zero-pt-in-ker : ∀ (i : Fin 2) → ∂₁ᶜ (proj₁ (Zero→H₁ zero-pt)) i ≡ T₀
zero-pt-in-ker fzero = refl
zero-pt-in-ker (fsuc fzero) = refl
-- 输出侧索引 Fin 2（C₀ᶜ = FAb 2 的两个分量）——∂₁ᶜ 按输出索引匹配

--------------------------------------------------------------------------------
-- §5. C4 完成度——完备性层第三块闭合
--
--   ✅ ker-from-T₁/T₂：核条件消去（无条件——⊗-cancel 非零消去）
--   ✅ 冗余性显式化：T₁/T₂ 两条件任一即可（∂₁ᶜ 单射的代数本质）
--   ✅ H₁-pt-trivial：逐点无条件平凡（Fin 1 穷尽——完备非抽样）
--   ✅ 零商对账：zero-pt-in-ker（与 KerImQuot/ChainQuotIso 对账）
--
--   完备性层终态：
--   C1 ✅（恰 2 存活）+ C2 ✅（分类+互异）+ C4 ✅（核平凡逐点）
--   ——「无第五根」ℤ 分解泛型化（③）与 Σ PathP 组装留 roadmap
--   （两者均为深水区；实例层完备性已全部在案）
--------------------------------------------------------------------------------
