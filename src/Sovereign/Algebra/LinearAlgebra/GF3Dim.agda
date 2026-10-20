{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3Dim
-- 有限 GF(3) 向量空间的**维数**基础（T4 的 b_n 组装配件，2026-10-20）
--
-- 设计原则
--   本库**不假设函数外延**（funext）⇒ 所有子空间陈述用**点态**形式：
--     组合 `Comb v c x = Σ_i c i ⊗ v i x`（逐点求和）
--     张成 `Span d v p  = Σ c, ∀ x, p x ≡ Comb v c x`
--   于是「`V` 由 `d` 个向量张成」是**可判定结构**，不需要商空间。
--
-- 本模块提供（§1–§4）
--   §1 组合 `Comb`
--   §2 张成 `Span`
--   §3 基本性质（零组合、单点组合）
--   §4 指示函数（`CoeffN n` 的标准基向量）与「按下标取值」的判据
--
-- 尚未提供（下一步）
--   秩-零化度 ⇒ `dim(ker F ∩ V_nA)` 的计数 —— 这是 b_n 组装的最后一步。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3Dim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate; ⊗-zeroˡ; ⊗-identityʳ; ⊕-identityˡ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus; sumFin; sumFin-cong; sumFin-zero)

CoeffN : ℕ → Set
CoeffN n = Torus n → Trit

--------------------------------------------------------------------------------
-- §1. 组合（逐点求和形式，避开 funext）
--------------------------------------------------------------------------------

Comb : ∀ {n} {d : ℕ} → (Fin d → CoeffN n) → (Fin d → Trit) → CoeffN n
Comb v c x = sumFin (λ i → c i ⊗ v i x)

--------------------------------------------------------------------------------
-- §2. 张成
--------------------------------------------------------------------------------

Span : ∀ {n} → (d : ℕ) → (Fin d → CoeffN n) → CoeffN n → Set
Span d v p = Σ (Fin d → Trit) (λ c → ∀ x → p x ≡ Comb v c x)

--------------------------------------------------------------------------------
-- §3. 基本性质
--------------------------------------------------------------------------------

-- 零组合给出零函数
comb-zero : ∀ {n d} (v : Fin d → CoeffN n) (x : Torus n) →
  Comb v (λ _ → T₀) x ≡ T₀
comb-zero {d = d} v x =
  trans (sumFin-cong {n = d} (λ i → ⊗-zeroˡ (v i x))) (sumFin-zero {d})

-- 零函数在任意张成里（取零组合）
zero-in-span : ∀ {n d} (v : Fin d → CoeffN n) →
  Span d v (λ _ → T₀)
zero-in-span v = (λ _ → T₀) , (λ x → sym (comb-zero v x))

-- 注：单个生成元 `v i` 落在张成里需要「δ 组合」，即 `c j = (i ≡ j ? T₁ : T₀)`，
--     依赖 `Fin d` 的可判定相等（下一步 §4 处理）。
