{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ChainHomo
-- M5 链同伦——零同伦实例（完整同伦条件，无省略）
--
-- 数学内容：
--   链同伦 h : Ψ ≃ Ψ' 的系数级条件（边界结果层面）：
--     ∂(h xs) ≡ b'(xs) ⊕ negate b(xs)     （b = ∂∘Ψ，b' = ∂∘Ψ'）
--   零同伦：h = 零映射、Ψ' = Ψ 时两侧**都定义性归零**：
--     左：∂ [] = T₀
--     右：b ⊕ negate b = T₀（negate-inv，GF(3) 群律 9 case）
--   ⟹ 零同伦闭合完整条件，无需省略。
--
-- 诚实边界：非平凡同伦需 h∂ 项的双级复合（h 作用在边界后的链上）
--   ——单级 List 表示下留 roadmap（M6 需双级链结构）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.ChainHomo where

open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Algebra.ListLaws
  using (map)
open import Sovereign.Algebra.ChainHom
  using (ChainHom; ∂; negChain)
open Sovereign.Algebra.ChainHom.Swap negChain renaming (sq-right to sq-right-neg)
open import Sovereign.Algebra.ListFunctor using (negate-hom)

--------------------------------------------------------------------------------
-- §1. negate 加法逆——a ⊕ negate a ≡ T₀（GF(3) 群律）
--------------------------------------------------------------------------------

negate-inv : ∀ (a : Trit) → a ⊕ negate a ≡ T₀
negate-inv T₀ = refl
negate-inv T₁ = refl
negate-inv T₂ = refl
-- negate T₁ = T₂：T₁⊕T₂ = T₀；negate T₂ = T₁：T₂⊕T₁ = T₀（⊕ 子句）——定义性

--------------------------------------------------------------------------------
-- §2. M5.1 零同伦——h = 零映射
--------------------------------------------------------------------------------

-- 零同伦映射：任何链映到空链
zero-h : List Trit → List Trit
zero-h _ = []

--------------------------------------------------------------------------------
-- §3. M5.2 同伦条件——零同伦闭合
--
--   条件（系数级）：∂(h xs) ≡ b' ⊕ negate b
--     b  = ∂(Ψ xs)   ——链映射 Ψ 的边界结果
--     b' = ∂(Ψ' xs)  ——链映射 Ψ' 的边界结果
--
--   零同伦（h = zero-h、Ψ' = Ψ = negChain）：
--     左 = ∂ [] = T₀
--     右 = b ⊕ negate b = T₀    [negate-inv]
--------------------------------------------------------------------------------

zeroHomo-cond : ∀ (xs : List Trit) →
                ∂ (zero-h xs)
                ≡ sq-right-neg xs
                  ⊕ negate (sq-right-neg xs)
zeroHomo-cond xs = sym (negate-inv (sq-right-neg xs))
-- 左：∂(zero-h xs) = ∂ [] = T₀（定义性）
-- 右：b ⊕ negate b，negate-inv b : b ⊕ negate b ≡ T₀，sym 反向即目标

--------------------------------------------------------------------------------
-- §4. M5.3 数值 sanity——具体链上的零同伦
--------------------------------------------------------------------------------

-- 2 项链：h 给空链，∂ 为 T₀
sanity-h : ∂ (zero-h (T₁ ∷ T₂ ∷ [])) ≡ T₀
sanity-h = refl

-- negate 链映射的边界在 2 项链上的自消去
sanity-b : sq-right-neg (T₁ ∷ T₂ ∷ [])
           ⊕ negate (sq-right-neg (T₁ ∷ T₂ ∷ []))
           ≡ T₀
sanity-b = negate-inv (sq-right-neg (T₁ ∷ T₂ ∷ []))

--------------------------------------------------------------------------------
-- §5. M5 完成度
--
--   ✅ negate-inv：GF(3) 加法逆群律（9→3 case refl）
--   ✅ 零同伦 zero-h + 完整同伦条件 zeroHomo-cond（无省略）
--   ✅ 数值 sanity ×2
--
--   复用链：ChainHom（∂/Swap.sq-right/negChain）+ negate-inv
--   下一步：M6 链同伦泛型化（非平凡 h 需双级链结构——roadmap）
--------------------------------------------------------------------------------
