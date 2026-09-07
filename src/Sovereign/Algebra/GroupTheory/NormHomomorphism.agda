{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.GroupTheory.NormHomomorphism
-- 范数坍缩的深度证明: 同态结构定理 (符号推理, 非穷举)
--
-- 深度层级 (对照项目标尺):
--   L1 (穷举 refl): NormExactSequence 的 12 个定理 —— 对 8 个 GF9Star 元素逐 case.
--   L2 (全称符号):   本模块 —— 对任意 x y : GF9Star 用同态性质符号推理.
--
-- 核心洞察: 范数坍缩的"核/像/封闭性"是范数同态的一般性质,
--   与具体元素无关. 由 GF9 层的 norm-mul (范数乘性) 与 *s-toGF9 (嵌入同态)
--   组合即可符号导出, 无需逐元素枚举.
--
-- 深度定理 (全部 ∀ 符号推理, 0 postulate):
--   norm-mul-s      : 范数是 GF9Star 乘法同态  N(x·y) = N(x)⊗N(y)
--   ker-closed      : 核对乘法封闭 (ker N 是子群)
--   ker-identity    : 单位元在核中
--   ker-inverse     : 逆元在核中 (核含逆)
--   ker-subgroup    : (封閉 + 单位 + 逆) ⟹ ker 是子群 [record 打包]
--
-- 依赖: GF9 (norm-mul, *s-toGF9, toGF9, inv, inv-correct), Trit

module Sovereign.Algebra.GroupTheory.NormHomomorphism where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊗_; ⊗-identityˡ; ⊗-identityʳ)
open import Sovereign.Algebra.GF9 using
  (GF9; GF9Star; toGF9; s1; _*s_; _^s_; inv; inv-correct; *s-comm; *s-toGF9;
   galoisNorm; norm-mul; _*gf9_)

--------------------------------------------------------------------------------
-- 深度定理 1. 范数是 GF9Star 乘法同态 (符号推理)
--
-- 证明 (纯符号, 3 步):
--   N(x·y) = N(toGF9(x·y))        [定义]
--          = N(toGF9 x *gf9 toGF9 y)  [*s-toGF9 同态]
--          = N(toGF9 x) ⊗ N(toGF9 y)  [norm-mul 乘性]
--------------------------------------------------------------------------------

norm-mul-s : ∀ x y → galoisNorm (toGF9 (x *s y)) ≡ galoisNorm (toGF9 x) ⊗ galoisNorm (toGF9 y)
norm-mul-s x y = begin
  galoisNorm (toGF9 (x *s y))
    ≡⟨ cong galoisNorm (*s-toGF9 x y) ⟩
  galoisNorm (toGF9 x *gf9 toGF9 y)
    ≡⟨ norm-mul (toGF9 x) (toGF9 y) ⟩
  galoisNorm (toGF9 x) ⊗ galoisNorm (toGF9 y)
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- 深度定理 2. 核是子群 (对乘法封闭)
--
-- 证明 (纯符号, 对任意 x y):
--   N(x)=T₁, N(y)=T₁ ⟹ N(x·y) = N(x)⊗N(y) = T₁⊗T₁ = T₁
--------------------------------------------------------------------------------

ker-closed : ∀ x y → galoisNorm (toGF9 x) ≡ T₁ → galoisNorm (toGF9 y) ≡ T₁
           → galoisNorm (toGF9 (x *s y)) ≡ T₁
ker-closed x y nx ny = begin
  galoisNorm (toGF9 (x *s y))
    ≡⟨ norm-mul-s x y ⟩
  galoisNorm (toGF9 x) ⊗ galoisNorm (toGF9 y)
    ≡⟨ cong₂ _⊗_ nx ny ⟩
  T₁ ⊗ T₁
    ≡⟨⟩
  T₁
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- 深度定理 3. 单位元在核中
--------------------------------------------------------------------------------

ker-identity : galoisNorm (toGF9 s1) ≡ T₁
ker-identity = refl

--------------------------------------------------------------------------------
-- 深度定理 4. 逆元在核中 (核含逆)
--
-- 证明 (纯符号, 对任意 x):
--   N(inv x) = N(inv x) ⊗ T₁           [⊗ 单位]
--            = N(inv x) ⊗ N(x)          [nx: N(x)=T₁]
--            = N(inv x · x)             [norm-mul-s 反向]
--            = N(s1)                    [inv-correct: x·inv x=s1, 交换律]
--            = T₁                       [ker-identity]
--------------------------------------------------------------------------------

ker-inverse : ∀ x → galoisNorm (toGF9 x) ≡ T₁ → galoisNorm (toGF9 (inv x)) ≡ T₁
ker-inverse x nx = begin
  galoisNorm (toGF9 (inv x))
    ≡⟨ sym (⊗-identityʳ (galoisNorm (toGF9 (inv x)))) ⟩
  galoisNorm (toGF9 (inv x)) ⊗ T₁
    ≡⟨ cong (galoisNorm (toGF9 (inv x)) ⊗_) (sym nx) ⟩
  galoisNorm (toGF9 (inv x)) ⊗ galoisNorm (toGF9 x)
    ≡⟨ sym (norm-mul-s (inv x) x) ⟩
  galoisNorm (toGF9 (inv x *s x))
    ≡⟨ cong (λ z → galoisNorm (toGF9 z)) (trans (*s-comm (inv x) x) (inv-correct x)) ⟩
  galoisNorm (toGF9 s1)
    ≡⟨ ker-identity ⟩
  T₁
  ∎
  where open ≡-Reasoning

--------------------------------------------------------------------------------
-- 深度定理 5. 核是子群 (record 打包: 封闭 + 单位 + 逆)
--------------------------------------------------------------------------------

record KernelSubgroup : Set where
  field
    closed   : ∀ x y → galoisNorm (toGF9 x) ≡ T₁ → galoisNorm (toGF9 y) ≡ T₁
                     → galoisNorm (toGF9 (x *s y)) ≡ T₁
    identity : galoisNorm (toGF9 s1) ≡ T₁
    inverse  : ∀ x → galoisNorm (toGF9 x) ≡ T₁ → galoisNorm (toGF9 (inv x)) ≡ T₁

ker-subgroup : KernelSubgroup
ker-subgroup = record
  { closed   = ker-closed
  ; identity = ker-identity
  ; inverse  = ker-inverse
  }

-- 0 postulate.
