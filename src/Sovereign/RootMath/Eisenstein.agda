{-# OPTIONS --guardedness #-}

-- | Sovereign.RootMath.Eisenstein
-- Eisenstein 整数环 Z[ω]:  a + b·ω, 其中 ω² + ω + 1 = 0, ω³ = 1
--
-- 宪法原则:
-- 1. 禁止使用浮点复数 (Data.Complex). 这是离散数学, 不能有连续统.
-- 2. Z[ω] 是 A₄ 特征标值的自然系数环:
--    - 三维表示 χ₃: 值 ∈ {3, 0, -1} ⊂ ℤ ⊂ Z[ω]
--    - 一维表示 χ₁': 值 ∈ {1, ω, ω²} ⊂ Z[ω]
-- 3. 乘法规则利用 ω² = -1 - ω, 避免任何 √3 或浮点.
-- 4. Z[ω] ≅ { (a,b) ∈ ℤ² | 乘法: (ac-bd) + (ad+bc-bd)ω }
--
-- 参考:
--   C++: /home/yanli/work/math/cpp/include/fixed_complex.h (Q16 Z[ω])
--   Agda: RootMath/AlgebraicComplex.agda (Gaussian / Sqrt3 pattern)

module Sovereign.RootMath.Eisenstein where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)

--------------------------------------------------------------------------------
-- 1. Eisenstein 整数类型
--------------------------------------------------------------------------------

-- Z[ω] = { a + b·ω | a,b ∈ ℤ }, ω² + ω + 1 = 0
-- 使用前缀构造器 eis 避免与 ℤ 的 + 前缀/中缀运算符冲突
record Eisenstein : Set where
  constructor eis
  field
    a : ℤ  -- 实部 (有理整数部)
    b : ℤ  -- ω 的系数

open Eisenstein public

-- 便捷构造: a + bω
pattern mkEis a b = eis a b

--------------------------------------------------------------------------------
-- 2. 基本常数
--------------------------------------------------------------------------------

0ᵉ : Eisenstein
0ᵉ = eis (+ 0) (+ 0)

1ᵉ : Eisenstein
1ᵉ = eis (+ 1) (+ 0)

ωᵉ : Eisenstein
ωᵉ = eis (+ 0) (+ 1)

ω²ᵉ : Eisenstein
ω²ᵉ = eis (-[1+ 0 ]) (-[1+ 0 ])  -- ω² = -1 - ω

-1ᵉ : Eisenstein
-1ᵉ = eis (-[1+ 0 ]) (+ 0)

3ᵉ : Eisenstein
3ᵉ = eis (+ 3) (+ 0)

--------------------------------------------------------------------------------
-- 3. 算术运算
--------------------------------------------------------------------------------

-- 加法: (a+bω) + (c+dω) = (a+c) + (b+d)ω
infixl 20 _+ᵉ_
_+ᵉ_ : Eisenstein → Eisenstein → Eisenstein
eis a b +ᵉ eis c d = eis (a + c) (b + d)

-- 乘法: (a+bω)(c+dω) = (ac-bd) + (ad+bc-bd)ω
-- 推导: = ac + adω + bcω + bdω²
--       = ac + (ad+bc)ω + bd(-1-ω)
--       = ac - bd + (ad+bc-bd)ω
infixl 25 _*ᵉ_
_*ᵉ_ : Eisenstein → Eisenstein → Eisenstein
eis a b *ᵉ eis c d = eis (a * c - b * d) (a * d + b * c - b * d)

--------------------------------------------------------------------------------
-- 4. 共轭
--------------------------------------------------------------------------------

-- 复共轭: ω ↔ ω²
-- conjω = ω² = -1-ω, 所以 conj(a+bω) = a + b·conjω = a + b(-1-ω) = (a-b) + (-b)ω
conjᵉ : Eisenstein → Eisenstein
conjᵉ (eis a b) = eis (a - b) ((+ 0) - b)

--------------------------------------------------------------------------------
-- 5. 代数恒等式 (关键: ω³=1, 1+ω+ω²=0)
--------------------------------------------------------------------------------

-- 1 + ω + ω² = 0
1+ω+ω²≡0 : (1ᵉ +ᵉ ωᵉ +ᵉ ω²ᵉ) ≡ 0ᵉ
1+ω+ω²≡0 = refl

-- ω² = ω * ω
ω²≡ω*ω : ωᵉ *ᵉ ωᵉ ≡ ω²ᵉ
ω²≡ω*ω = refl

-- ω³ = 1
ω³≡1 : ωᵉ *ᵉ ωᵉ *ᵉ ωᵉ ≡ 1ᵉ
ω³≡1 = refl

-- conj(ω) = ω²
conj-ω≡ω² : conjᵉ ωᵉ ≡ ω²ᵉ
conj-ω≡ω² = refl

-- conj(ω²) = ω
conj-ω²≡ω : conjᵉ ω²ᵉ ≡ ωᵉ
conj-ω²≡ω = refl

-- ω * ω² = 1 (因为 ω³=1)
ω*ω²≡1 : (ωᵉ *ᵉ ω²ᵉ) ≡ 1ᵉ
ω*ω²≡1 = refl

--------------------------------------------------------------------------------
-- 6. A₄ 特征标表的值 (预定义常数)
--------------------------------------------------------------------------------

-- 用于三维不可约表示 χ₃
χ₃-1 : Eisenstein  -- χ₃(identity) = 3
χ₃-1 = 3ᵉ

χ₃-3cycle : Eisenstein  -- χ₃(3-cycle) = 0
χ₃-3cycle = 0ᵉ

χ₃-2trans : Eisenstein  -- χ₃(double transposition) = -1
χ₃-2trans = -1ᵉ

-- 用于一维不可约表示 χ₁ (平凡)
χ₁-val : Eisenstein  -- 对所有元素 = 1
χ₁-val = 1ᵉ

-- 用于一维不可约表示 χ₁' (3-cycle → ω)
χ₁'-identity : Eisenstein
χ₁'-identity = 1ᵉ

χ₁'-3cycle : Eisenstein   -- Rot zero zero 类的值
χ₁'-3cycle = ωᵉ

χ₁'-3cycle2 : Eisenstein  -- Rot zero (suc zero) 类的值 = ω²
χ₁'-3cycle2 = ω²ᵉ

χ₁'-2trans : Eisenstein   -- double transposition → 1
χ₁'-2trans = 1ᵉ

-- 用于一维不可约表示 χ₁'' (χ₁' 的复共轭)
χ₁''-identity : Eisenstein
χ₁''-identity = 1ᵉ

χ₁''-3cycle : Eisenstein   -- 3-cycle → ω²
χ₁''-3cycle = ω²ᵉ

χ₁''-3cycle2 : Eisenstein  -- 3-cycle² → ω
χ₁''-3cycle2 = ωᵉ

χ₁''-2trans : Eisenstein
χ₁''-2trans = 1ᵉ
