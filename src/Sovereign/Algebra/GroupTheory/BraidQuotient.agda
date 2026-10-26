{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.BraidQuotient
-- **eval 尊重 braid 同余**（B₃ 的桥在词层的那一半）。
--
-- 本件现在只保留「求值与同余的关系」；同余本体（`_≈b_` 与全部词论件）
-- 已抽到 `BraidCongruence`（零 Trit 依赖），故 cubical 商模块不必导入本件。
--
-- 包含：eval-resp（11 构造子归纳）/ eval-W-class（整类映到 −I）
-- 0 postulate / 0 hole。

module Sovereign.Algebra.GroupTheory.BraidQuotient where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Sovereign.Synthesis.Representation.SL23Cayley using (mulMat2)

open import Sovereign.Algebra.GroupTheory.Word using (Word; _++W_)
open import Sovereign.Algebra.GroupTheory.BraidCongruence using
  ( _≈b_; b-refl; b-sym; b-trans; b-same
  ; b-appendˡ; b-appendʳ
  ; b-cancel-a; b-cancel-b; b-cancel-ai; b-cancel-bi
  ; b-braid )

open import Sovereign.Algebra.GroupTheory.BraidToSL23 using
  ( eval; eval-++W; eval-braid
  ; eval-cancel-a; eval-cancel-b; eval-cancel-ai; eval-cancel-bi
  ; wWord; eval-W-word; negI )

--------------------------------------------------------------------------------
-- eval 尊重同余（11 个构造子）
--------------------------------------------------------------------------------

eval-resp : ∀ {w v} → w ≈b v → eval w ≡ eval v
eval-resp b-refl            = refl
eval-resp (b-sym h)         = sym (eval-resp h)
eval-resp (b-trans h1 h2)   = trans (eval-resp h1) (eval-resp h2)
eval-resp (b-appendˡ q h) =
  trans (eval-++W _ q)                                              -- 拆右接
    (trans (cong (λ T → mulMat2 T (eval q)) (eval-resp h))
           (sym (eval-++W _ q)))
eval-resp (b-appendʳ p h) =
  trans (eval-++W p _)                                              -- 拆左接
    (trans (cong (mulMat2 (eval p)) (eval-resp h))
           (sym (eval-++W p _)))
eval-resp (b-same e)        = cong eval e
eval-resp (b-cancel-a w)    = eval-cancel-a w
eval-resp (b-cancel-b w)    = eval-cancel-b w
eval-resp (b-cancel-ai w)   = eval-cancel-ai w
eval-resp (b-cancel-bi w)   = eval-cancel-bi w
eval-resp b-braid           = eval-braid

-- 推论：W 的整个同余类都映到 −I
eval-W-class : ∀ w → w ≈b wWord → eval w ≡ negI
eval-W-class w h = trans (eval-resp h) eval-W-word
