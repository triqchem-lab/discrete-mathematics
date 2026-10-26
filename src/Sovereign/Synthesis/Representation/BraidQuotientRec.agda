{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Representation.BraidQuotientRec
-- **B₃ 商的递归原理**：任何从词出发的**同态**，只要它在生成元上与指派一致、
-- 且把辫关系送到目标群的 `≈`，就必须尊重 `≈b`——
-- 即「按 `≈b` 的类定义映射」是良定义的。
--
-- 这是「商群的泛性质」中**可判定的一半**（下降的良定义性 + 递归式）；
-- 完整泛性质还需 `Word/≈b` 作为对象——那已在
-- `BraidGroupSetoid.word-setoid-group` 给出（setoid 形态，非 HIT）。
--
-- 分两层模块：外层取 sg 并 open（使 `≈`/`⋆`/`refl≈` 进入作用域），
-- 内层再取「同态 φ + 六条约束」。否则参数列表里写不出 `≈`（Agda 顺序作用域）。
--
-- 策略：结构归纳 + setoid 替换（⋆-cong / assoc / invʳ / unitʳ），每项 ≤3 步
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.BraidQuotientRec where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import _PN15 using (SetoidGroupData)

open import Sovereign.Algebra.GroupTheory.BraidCongruence using
  ( _≈b_; b-refl; b-sym; b-trans; b-same
  ; b-appendˡ; b-appendʳ
  ; b-cancel-a; b-cancel-b; b-cancel-ai; b-cancel-bi
  ; b-braid )
open import Sovereign.Algebra.GroupTheory.Word using
  ( Word; ε; _·a; _·b; _·ai; _·bi; _++W_; aba; bab )

module QuotientRec (sg : SetoidGroupData) where

  open SetoidGroupData sg

  module Inner
    (f       : Bool → Carrier)
    (φ       : Word → Carrier)
    (φ-hom   : ∀ p q → φ (p ++W q) ≈ φ p ⋆ φ q)
    (φ-a     : φ (ε ·a)  ≈ f true)
    (φ-b     : φ (ε ·b)  ≈ f false)
    (φ-ai    : φ (ε ·ai) ≈ ι (f true))
    (φ-bi    : φ (ε ·bi) ≈ ι (f false))
    (φ-braid : φ aba ≈ φ bab)
    where

    -- 吸收引理：φ w ⋆ (g ⋆ ι g) ≈ φ w（右逆 + 单位）
    absorb : ∀ {w} (g : Carrier) → φ w ⋆ (g ⋆ ι g) ≈ φ w
    absorb {w} g =
      trans≈ (⋆-cong refl≈ (invʳ g)) (unitʳ (φ w))

    -- 反序吸收：φ w ⋆ (ι g ⋆ g) ≈ φ w（左逆 + 单位）
    absorbˡ : ∀ {w} (g : Carrier) → φ w ⋆ (ι g ⋆ g) ≈ φ w
    absorbˡ {w} g =
      trans≈ (⋆-cong refl≈ (invˡ g)) (unitʳ (φ w))

    --------------------------------------------------------------------------
    -- 主定理：φ 尊重 ≈b（8 个构造子）
    --------------------------------------------------------------------------

    resp : ∀ {w v} → w ≈b v → φ w ≈ φ v
    resp b-refl          = refl≈
    resp (b-sym h)       = sym≈ (resp h)
    resp (b-trans h1 h2) = trans≈ (resp h1) (resp h2)

    resp (b-same {w} {v} e) = subst (λ z → φ w ≈ φ z) e refl≈

    resp (b-appendˡ q h) =
      trans≈ (φ-hom _ q)
        (trans≈ (⋆-cong (resp h) refl≈)
                (sym≈ (φ-hom _ q)))

    resp (b-appendʳ p h) =
      trans≈ (φ-hom p _)
        (trans≈ (⋆-cong refl≈ (resp h))
                (sym≈ (φ-hom p _)))

    resp (b-cancel-a w) =
      trans≈ (φ-hom (w ·a) (ε ·ai))
        (trans≈ (⋆-cong (φ-hom w (ε ·a)) φ-ai)
          (trans≈ (assoc (φ w) (φ (ε ·a)) (ι (f true)))
                  (trans≈ (⋆-cong refl≈ (⋆-cong φ-a refl≈))
                          (absorb (f true)))))

    resp (b-cancel-b w) =
      trans≈ (φ-hom (w ·b) (ε ·bi))
        (trans≈ (⋆-cong (φ-hom w (ε ·b)) φ-bi)
          (trans≈ (assoc (φ w) (φ (ε ·b)) (ι (f false)))
                  (trans≈ (⋆-cong refl≈ (⋆-cong φ-b refl≈))
                          (absorb (f false)))))

    resp (b-cancel-ai w) =
      trans≈ (φ-hom (w ·ai) (ε ·a))
        (trans≈ (⋆-cong (φ-hom w (ε ·ai)) φ-a)
          (trans≈ (assoc (φ w) (φ (ε ·ai)) (f true))
                  (trans≈ (⋆-cong refl≈ (⋆-cong φ-ai refl≈))
                          (absorbˡ (f true)))))

    resp (b-cancel-bi w) =
      trans≈ (φ-hom (w ·bi) (ε ·b))
        (trans≈ (⋆-cong (φ-hom w (ε ·bi)) φ-b)
          (trans≈ (assoc (φ w) (φ (ε ·bi)) (f false))
                  (trans≈ (⋆-cong refl≈ (⋆-cong φ-bi refl≈))
                          (absorbˡ (f false)))))

    resp b-braid = φ-braid
