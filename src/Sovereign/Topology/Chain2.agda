{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Chain2
-- M6 双级链结构——非平凡链同伦（h∂ 项完整，无省略）
--
-- 数学内容：
--   双级链：上链（List Trit）经边界 ∂₁ 映到下链结果（单 Trit）。
--   完整同伦条件（两项都在）：
--     ∂₁ f' (map h xs)  ⊕  h (∂₁ f xs)  ≡  Ψ' xs ⊕ negate (Ψ xs)
--     └── ∂h 项 ──┘        └─ h∂ 项 ─┘
--   M5 零同伦的 h∂ 项在此显式出现（h 作用于边界结果值）。
--
--   非平凡实例：f = f' = T₁、h = T₂、Ψ = ∂₁ f、Ψ' = ∂₁ f' ∘ map h
--   满足条件（依赖 sum-distr：⊗ 对 ⊕ 求和的分配）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.Chain2 where

open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; cong₂; sym)

open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate
        ; ⊗-distribˡ-⊕)
open import Sovereign.Algebra.ListLaws
  using (map; foldr; sum⊕)

--------------------------------------------------------------------------------
-- §1. 上链边界——∂₁（面系数 f 的加权和）
--------------------------------------------------------------------------------

∂₁ : (f : Trit → Trit) → List Trit → Trit
∂₁ f xs = foldr (λ x acc → f x ⊕ acc) T₀ xs

-- f = 恒等时 ∂₁ 退化为普通求和（定义性一致）
∂₁-id : ∀ xs → ∂₁ (λ x → x) xs ≡ sum⊕ xs
∂₁-id []       = refl
∂₁-id (x ∷ xs) = refl

--------------------------------------------------------------------------------
-- §2. 线性引理——⊗ 对 ⊕ 求和的分配（sum-distr）
--
--   g ⊗ sum⊕ xs ≡ sum⊕ (map (g ⊗_) xs)
--   归纳：⊗-distribˡ-⊕ 分配头项 + IH。
--------------------------------------------------------------------------------

⊗-zeroʳ : ∀ (a : Trit) → a ⊗ T₀ ≡ T₀
⊗-zeroʳ T₀ = refl
⊗-zeroʳ T₁ = refl
⊗-zeroʳ T₂ = refl

sum-distr : ∀ (g : Trit) (xs : List Trit) →
            g ⊗ sum⊕ xs ≡ sum⊕ (map (λ x → g ⊗ x) xs)
sum-distr g []       = ⊗-zeroʳ g
sum-distr g (x ∷ xs) =
  trans (⊗-distribˡ-⊕ g x (sum⊕ xs))
        (cong (λ u → (g ⊗ x) ⊕ u) (sum-distr g xs))
-- g⊗(x⊕s) = (g⊗x)⊕(g⊗s) = (g⊗x)⊕sum⊕(map…)  [分配 + IH]

--------------------------------------------------------------------------------
-- §3. M6 完整同伦条件——∂h 项与 h∂ 项显式并存
--------------------------------------------------------------------------------

module Homo2 (f f' : Trit → Trit) (h : Trit → Trit) where

  -- ∂h 项：同伦作用后经 f' 出口求和
  ∂h-term : List Trit → Trit
  ∂h-term xs = ∂₁ f' (map h xs)

  -- h∂ 项：上链边界结果经同伦作用
  h∂-term : List Trit → Trit
  h∂-term xs = h (∂₁ f xs)

  -- 两个链映射：Ψ = ∂₁ f，Ψ' = ∂h-term
  Ψ  : List Trit → Trit
  Ψ  xs = ∂₁ f xs
  Ψ' : List Trit → Trit
  Ψ' xs = ∂h-term xs

  -- 完整同伦条件（陈述）：∂h + h∂ ≡ Ψ' − Ψ
  HomoCond : Set
  HomoCond = ∀ xs → ∂h-term xs ⊕ h∂-term xs ≡ Ψ' xs ⊕ negate (Ψ xs)

--------------------------------------------------------------------------------
-- §4. 非平凡实例——f = f' = T₁、h = T₂
--
--   验证：
--   ∂h 项 = ∂₁ (map T₂ xs) = sum⊕ (map (T₂⊗_) xs)   [∂₁-sum + h=T₂⊗_]
--         = T₂ ⊗ sum⊕ xs                             [sum-distr 反向]
--   h∂ 项 = T₂ ⊗ sum⊕ xs                              [h = T₂⊗_]
--   左 = (T₂⊗b) ⊕ (T₂⊗b) —— 而右 = Ψ' ⊕ negate Ψ = (T₂⊗b) ⊕ negate b
--   由 negate b = T₂⊗b（GF(3) 群律）两侧相等 ✓
--------------------------------------------------------------------------------

negate-⊗T₂ : ∀ (a : Trit) → negate a ≡ T₂ ⊗ a
negate-⊗T₂ T₀ = refl
negate-⊗T₂ T₁ = refl
negate-⊗T₂ T₂ = refl
-- negate T₁ = T₂ = T₂⊗T₁；negate T₂ = T₁ = T₂⊗T₂；negate T₀ = T₀ = T₂⊗T₀

-- ⚠ 设计注记：h 必须取线性形式 λ x → T₂ ⊗ x 而非常数 T₂
--   （常数版不保 T₀：T₂⊗T₀ = T₀ ≠ T₂——线性性破坏）
--   线性 h 下 ∂h 项经 sum-distr 精确等于 T₂ ⊗ sum⊕ xs。

module HomoT2 where
  f  = λ (x : Trit) → x        -- 恒等面系数：∂₁ f = sum⊕（定义性）
  f' = λ (x : Trit) → x
  h  = λ (x : Trit) → T₂ ⊗ x   -- 线性同伦（保 T₀）

  open Homo2 f f' h

  -- ✅ 完整同伦条件成立（非平凡实例：h = negate 型线性映射）
  -- ∂h 项 = sum⊕ (map (T₂⊗_) ys) = T₂ ⊗ sum⊕ ys   [∂₁-id + sum-distr 反向]
  -- h∂ 项 = T₂ ⊗ sum⊕ ys                           [h 直接应用]
  -- 右  = Ψ' ys ⊕ negate (Ψ ys)
  --     = (T₂⊗b) ⊕ negate b = (T₂⊗b) ⊕ (T₂⊗b)     [negate-⊗T₂]
  -- 左  = (T₂⊗b) ⊕ (T₂⊗b)                          [两项同值]
  -- 两侧定义性一致 + negate-⊗T₂ 重述
  homo-holds : HomoCond
  homo-holds ys = cong₂ _⊕_ refl (sym (negate-⊗T₂ (∂₁ f ys)))
