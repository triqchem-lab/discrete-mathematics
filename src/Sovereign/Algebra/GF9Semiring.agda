{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GF9Semiring
-- GF(9) 交换半环实例 — "只有加乘，无减除" 的代数形式
--
-- CommSemiring 记录不含加法逆元 (neg) 和乘法逆元 (inv)，
-- 只含: 加乘运算、零元/幺元、结合/交换、单位、分配、零乘吸收。
-- 对应语料: word_46 "没有减号和除号……只有加号和乘号"
--
-- 依赖: GF9.agda (域公理) + UniversalAlgebra.agda (CommSemiring 记录)
-- 0 postulate.

module Sovereign.Algebra.GF9Semiring where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_,_)

open import Sovereign.Base.Trit using (T₀; T₁; T₂)
open import Sovereign.Algebra.UniversalAlgebra using (CommSemiring)
open import Sovereign.Algebra.GF9
  using ( GF9; _+gf9_; _*gf9_; gf9-zero; gf9-one
        ; +gf9-assoc; +gf9-comm; +gf9-identityˡ; +gf9-identityʳ
        ; *gf9-assoc; *gf9-comm; *gf9-identityˡ; *gf9-identityʳ
        ; *gf9-distribˡ-+gf9; *gf9-distribʳ-+gf9
        )

-- distribʳ 的变量顺序: CommSemiring 要求 (y+z)*x = y*x + z*x
-- GF9 提供: (x+y)*z = x*z + y*z — 同构，需重排变量
distribʳ-gf9 : ∀ x y z → (y +gf9 z) *gf9 x ≡ (y *gf9 x) +gf9 (z *gf9 x)
distribʳ-gf9 x y z = *gf9-distribʳ-+gf9 y z x

-- 零吸收 (GF9 无此引理, 9 case 穷举)
gf9-zero-mulˡ : ∀ y → gf9-zero *gf9 y ≡ gf9-zero
gf9-zero-mulˡ (T₀ , T₀) = refl
gf9-zero-mulˡ (T₀ , T₁) = refl
gf9-zero-mulˡ (T₀ , T₂) = refl
gf9-zero-mulˡ (T₁ , T₀) = refl
gf9-zero-mulˡ (T₁ , T₁) = refl
gf9-zero-mulˡ (T₁ , T₂) = refl
gf9-zero-mulˡ (T₂ , T₀) = refl
gf9-zero-mulˡ (T₂ , T₁) = refl
gf9-zero-mulˡ (T₂ , T₂) = refl

gf9-zero-mulʳ : ∀ y → y *gf9 gf9-zero ≡ gf9-zero
gf9-zero-mulʳ (T₀ , T₀) = refl
gf9-zero-mulʳ (T₀ , T₁) = refl
gf9-zero-mulʳ (T₀ , T₂) = refl
gf9-zero-mulʳ (T₁ , T₀) = refl
gf9-zero-mulʳ (T₁ , T₁) = refl
gf9-zero-mulʳ (T₁ , T₂) = refl
gf9-zero-mulʳ (T₂ , T₀) = refl
gf9-zero-mulʳ (T₂ , T₁) = refl
gf9-zero-mulʳ (T₂ , T₂) = refl

gf9-semiring : CommSemiring GF9
gf9-semiring = record
  { _+_      = _+gf9_
  ; _*_      = _*gf9_
  ; zero     = gf9-zero
  ; one      = gf9-one
  ; +-assoc  = +gf9-assoc
  ; +-comm   = +gf9-comm
  ; +-idˡ    = +gf9-identityˡ
  ; +-idʳ    = +gf9-identityʳ
  ; *-assoc  = *gf9-assoc
  ; *-comm   = *gf9-comm
  ; *-idˡ    = *gf9-identityˡ
  ; *-idʳ    = *gf9-identityʳ
  ; distribˡ = *gf9-distribˡ-+gf9
  ; distribʳ = distribʳ-gf9
  ; zeroˡ    = gf9-zero-mulˡ
  ; zeroʳ    = gf9-zero-mulʳ
  }

-- 0 postulate.
