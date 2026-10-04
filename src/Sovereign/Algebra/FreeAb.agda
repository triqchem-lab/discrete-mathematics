{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.FreeAb
-- 任务书第二层·2.1 基座：GF(3)-系数自由阿贝尔模（FreeAb）
--
-- 数学背景：单纯链群 C_k(K; GF(3)) 的载体——n 个生成元上的 GF(3)-自由模
--   FAb n = Fin n → Trit（系数逐点 ∈ GF(3)，Trit 即 GF(3) 加法群）。
--   这是泛型边界算子 ∂（P2.1 收官）与 P2.5 主定理解阻塞的基座载体。
--
-- 展示群风格（docs/duodecimal/11）：载体 = 生成元集 Fin n 上的 GF(3)-系数
--   函数；律为逐点陈述（规避 funext——无函数外延公理）；核对 refl；0 postulate。
--
-- 设计要点（fable5 多路径决策）：
--   路径 B（本模块）：FreeAb 真泛型（任意 n）+ 逐点律；
--   路径 A（roadmap）：全泛型 SimplicialComplex record + 面恒等式字段。
--
-- ⚠ 诚实边界：函数相等一律用逐点陈述（∀ i → ...）——本库无 funext，
--   整体函数相等（如 x ≡ zeroᶠ）不可证也不需要（∂∂=0 逐点即闭合）。
--
-- 复用：Base/Trit（⊕ ⊗ negate 全律已证）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.FreeAb where

open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit
  using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate;
         ⊕-comm; ⊕-assoc; ⊕-identityˡ; ⊕-identityʳ)

--------------------------------------------------------------------------------
-- §1. 载体：FAb n = Fin n → Trit（n 生成元的 GF(3)-自由模）
--------------------------------------------------------------------------------

FAb : ℕ → Set
FAb n = Fin n → Trit

--------------------------------------------------------------------------------
-- §2. 逐点代数结构
--------------------------------------------------------------------------------

-- 零向量
zeroᶠ : ∀ n → FAb n
zeroᶠ n = λ _ → T₀

-- 逐点加法
_+ᶠ_ : ∀ {n} → FAb n → FAb n → FAb n
(x +ᶠ y) i = x i ⊕ y i

-- 逐点取负（GF(3)：negate = ×T₂，negate 自逆）
negᶠ : ∀ {n} → FAb n → FAb n
negᶠ x = λ i → negate (x i)

--------------------------------------------------------------------------------
-- §3. GF(3) 符号消去根基：2a + a ≡ 0（三循环，三 case refl）
--------------------------------------------------------------------------------

neg-add : ∀ (a : Trit) → (a ⊗ T₂) ⊕ a ≡ T₀
neg-add T₀ = refl
neg-add T₁ = refl
neg-add T₂ = refl

neg-selfinv : ∀ (a : Trit) → negate (negate a) ≡ a
neg-selfinv T₀ = refl
neg-selfinv T₁ = refl
neg-selfinv T₂ = refl

--------------------------------------------------------------------------------
-- §4. 逐点律（无 funext：全部 ∀ i 点态陈述）
--------------------------------------------------------------------------------

+ᶠ-comm : ∀ {n} (x y : FAb n) (i : Fin n) → (x +ᶠ y) i ≡ (y +ᶠ x) i
+ᶠ-comm x y i = ⊕-comm (x i) (y i)

+ᶠ-assoc : ∀ {n} (x y z : FAb n) (i : Fin n) →
           ((x +ᶠ y) +ᶠ z) i ≡ (x +ᶠ (y +ᶠ z)) i
+ᶠ-assoc x y z i = ⊕-assoc (x i) (y i) (z i)

+ᶠ-identityˡ : ∀ {n} (x : FAb n) (i : Fin n) → (zeroᶠ n +ᶠ x) i ≡ x i
+ᶠ-identityˡ x i = ⊕-identityˡ (x i)

+ᶠ-identityʳ : ∀ {n} (x : FAb n) (i : Fin n) → (x +ᶠ zeroᶠ n) i ≡ x i
+ᶠ-identityʳ x i = ⊕-identityʳ (x i)
