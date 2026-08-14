{-# OPTIONS --rewriting --guardedness #-}

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

open import Data.Integer using (ℤ; +0; +[1+_]; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties
  using (+-comm; +-assoc; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ;
         *-comm; *-assoc; *-identityˡ; *-identityʳ;
         *-distribˡ-+; *-distribʳ-+; neg-distrib-+; neg-involutive; *-zeroˡ; *-zeroʳ)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; _≢_; cong; cong₂; sym; trans; subst; module ≡-Reasoning)

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


--------------------------------------------------------------------------------
-- 7. 环公理 8 条 + 范数乘性 + 6 单位 (P1-4, 12F/11R)
--------------------------------------------------------------------------------

open ≡-Reasoning

0ℤ : ℤ
0ℤ = + 0

-ᵉ_ : Eisenstein → Eisenstein
-ᵉ eis a b = eis (- a) (- b)

-- x·(−y) ≡ −(x·y) 与 (−x)·y ≡ −(x·y)
neg-*-r : ∀ x y → x * (- y) ≡ - (x * y)
neg-*-r x y = begin
  x * (- y)
    ≡⟨ sym (+-identityʳ (x * (- y))) ⟩
  x * (- y) + 0ℤ
    ≡⟨ cong ((λ t → (x * (- y)) + t)) (sym (+-inverseʳ (x * y))) ⟩
  x * (- y) + (x * y + (- (x * y)))
    ≡⟨ sym (+-assoc (x * (- y)) (x * y) (- (x * y))) ⟩
  (x * (- y) + x * y) + (- (x * y))
    ≡⟨ cong (_+ (- (x * y))) (sym (*-distribˡ-+ x (- y) y)) ⟩
  x * (- y + y) + (- (x * y))
    ≡⟨ cong (λ t → (x * t) + (- (x * y))) (+-comm (- y) y) ⟩
  x * (y + (- y)) + (- (x * y))
    ≡⟨ cong (λ t → (x * t) + (- (x * y))) (+-inverseʳ y) ⟩
  x * 0ℤ + (- (x * y))
    ≡⟨ cong (_+ (- (x * y))) (trans (*-comm x 0ℤ) (*-identityˡ 0ℤ)) ⟩
  0ℤ + (- (x * y))
    ≡⟨ +-identityˡ (- (x * y)) ⟩
  - (x * y)
  ∎

neg-*-l : ∀ x y → (- x) * y ≡ - (x * y)
neg-*-l x y = begin
  (- x) * y
    ≡⟨ *-comm (- x) y ⟩
  y * (- x)
    ≡⟨ neg-*-r y x ⟩
  - (y * x)
    ≡⟨ cong -_ (*-comm y x) ⟩
  - (x * y)
  ∎

-- (1) 加法交换
+ᵉ-comm : ∀ x y → x +ᵉ y ≡ y +ᵉ x
+ᵉ-comm (eis a b) (eis c d) = cong₂ eis (+-comm a c) (+-comm b d)

-- (2) 加法结合
+ᵉ-assoc : ∀ x y z → (x +ᵉ y) +ᵉ z ≡ x +ᵉ (y +ᵉ z)
+ᵉ-assoc (eis a b) (eis c d) (eis e f) = cong₂ eis (+-assoc a c e) (+-assoc b d f)

-- (3) 加法单位
+ᵉ-identityˡ : ∀ x → 0ᵉ +ᵉ x ≡ x
+ᵉ-identityˡ (eis a b) = cong₂ eis (+-identityˡ a) (+-identityˡ b)

+ᵉ-identityʳ : ∀ x → x +ᵉ 0ᵉ ≡ x
+ᵉ-identityʳ (eis a b) = cong₂ eis (+-identityʳ a) (+-identityʳ b)

-- (4) 加法逆元
+ᵉ-inverseˡ : ∀ x → (-ᵉ x) +ᵉ x ≡ 0ᵉ
+ᵉ-inverseˡ (eis a b) = cong₂ eis (+-inverseˡ a) (+-inverseˡ b)

+ᵉ-inverseʳ : ∀ x → x +ᵉ (-ᵉ x) ≡ 0ᵉ
+ᵉ-inverseʳ (eis a b) = cong₂ eis (+-inverseʳ a) (+-inverseʳ b)

-- (5) 乘法交换
*ᵉ-comm : ∀ x y → x *ᵉ y ≡ y *ᵉ x
*ᵉ-comm (eis a b) (eis c d) = cong₂ eis comp1 comp2
  where
    comp1 : a * c - b * d ≡ c * a - d * b
    comp1 = cong₂ _-_ (*-comm a c) (*-comm b d)
    comp2 : a * d + b * c - b * d ≡ c * b + d * a - d * b
    comp2 = begin
      a * d + b * c - b * d
        ≡⟨ cong₂ (λ x y → x + y - b * d) (*-comm a d) (*-comm b c) ⟩
      d * a + c * b - b * d
        ≡⟨ cong (λ t → d * a + c * b - t) (*-comm b d) ⟩
      d * a + c * b - d * b
        ≡⟨ cong (λ t → t - d * b) (+-comm (d * a) (c * b)) ⟩
      c * b + d * a - d * b
      ∎

-- (6) 乘法结合: 两侧展开为同一规范型
--   comp1 规范型: ace + (−bde) + (−adf) + (−bcf) + bdf
--   comp2 规范型: acf + ade + (−adf) + bce + (−bdf) + (−bcf) + (−bde) + bdf
*ᵉ-assoc : ∀ x y z → (x *ᵉ y) *ᵉ z ≡ x *ᵉ (y *ᵉ z)
*ᵉ-assoc (eis a b) (eis c d) (eis e f) = cong₂ eis comp1 comp2
  where
    comp1 : (a * c - b * d) * e - (a * d + b * c - b * d) * f
            ≡ a * (c * e - d * f) - b * (c * f + d * e - d * f)
    comp1 = begin
      (a * c - b * d) * e - (a * d + b * c - b * d) * f
        ≡⟨⟩
      (a * c + (- (b * d))) * e - ((a * d + b * c) + (- (b * d))) * f
        ≡⟨ cong₂ _-_ (*-distribʳ-+ e (a * c) (- (b * d)))
                     (*-distribʳ-+ f (a * d + b * c) (- (b * d))) ⟩
      ((a * c) * e + (- (b * d)) * e) - (((a * d + b * c) * f) + ((- (b * d)) * f))
        ≡⟨ cong₂ _-_ (cong₂ _+_ (*-assoc a c e) (neg-*-l (b * d) e))
                     (cong₂ _+_ (*-distribʳ-+ f (a * d) (b * c)) (neg-*-l (b * d) f)) ⟩
      (a * (c * e) + (- (b * d * e))) - (((a * d) * f + (b * c) * f) + (- ((b * d) * f)))
        ≡⟨ cong₂ _-_ (cong₂ _+_ (refl {x = a * (c * e)}) (cong -_ (*-assoc b d e)))
                     (cong₂ _+_ (cong₂ _+_ (*-assoc a d f) (*-assoc b c f)) (cong -_ (*-assoc b d f))) ⟩
      (a * (c * e) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f))))
        ≡⟨ cong (λ t → (a * (c * e) + (- (b * (d * e)))) - t)
                (+-assoc (a * (d * f)) (b * (c * f)) (- (b * (d * f)))) ⟩
      (a * (c * e) + (- (b * (d * e)))) - (a * (d * f) + (b * (c * f) + (- (b * (d * f)))))
        ≡⟨⟩
      (a * (c * e) + (- (b * (d * e)))) + (- (a * (d * f) + (b * (c * f) + (- (b * (d * f))))))
        ≡⟨ cong (λ t → (a * (c * e) + (- (b * (d * e)))) + t)
                (neg-distrib-+ (a * (d * f)) (b * (c * f) + (- (b * (d * f))))) ⟩
      (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + (- (b * (c * f) + (- (b * (d * f))))))
        ≡⟨ cong (λ t → (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + t))
                (neg-distrib-+ (b * (c * f)) (- (b * (d * f)))) ⟩
      (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + ((- (b * (c * f))) + (- (- (b * (d * f))))))
        ≡⟨ cong (λ t → (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + ((- (b * (c * f))) + t)))
                (neg-involutive (b * (d * f))) ⟩
      (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + ((- (b * (c * f))) + (b * (d * f))))
        ≡⟨ canonical1 a b c d e f ⟩
      a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
        ≡⟨ unfold1 a b c d e f ⟩
      a * (c * e - d * f) - b * (c * f + d * e - d * f)
      ∎ where
        canonical1 : ∀ a b c d e f →
          (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + ((- (b * (c * f))) + (b * (d * f))))
          ≡ a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
        canonical1 a b c d e f = begin
          (a * (c * e) + (- (b * (d * e)))) + ((- (a * (d * f))) + ((- (b * (c * f))) + (b * (d * f))))
            ≡⟨ +-assoc (a * (c * e)) (- (b * (d * e))) ((- (a * (d * f))) + ((- (b * (c * f))) + (b * (d * f)))) ⟩
          a * (c * e) + ((- (b * (d * e))) + ((- (a * (d * f))) + ((- (b * (c * f))) + (b * (d * f)))))
            ≡⟨ cong (λ t → a * (c * e) + t) (sym (+-assoc (- (b * (d * e))) (- (a * (d * f))) ((- (b * (c * f))) + (b * (d * f))))) ⟩
          a * (c * e) + (((- (b * (d * e))) + (- (a * (d * f)))) + ((- (b * (c * f))) + (b * (d * f))))
            ≡⟨ cong (λ t → a * (c * e) + (t + ((- (b * (c * f))) + (b * (d * f))))) (+-comm (- (b * (d * e))) (- (a * (d * f)))) ⟩
          a * (c * e) + (((- (a * (d * f))) + (- (b * (d * e)))) + ((- (b * (c * f))) + (b * (d * f))))
            ≡⟨ cong (λ t → a * (c * e) + t) (+-assoc (- (a * (d * f))) (- (b * (d * e))) ((- (b * (c * f))) + (b * (d * f)))) ⟩
          a * (c * e) + ((- (a * (d * f))) + ((- (b * (d * e))) + ((- (b * (c * f))) + (b * (d * f)))))
            ≡⟨ cong (λ t → a * (c * e) + ((- (a * (d * f))) + t)) (sym (+-assoc (- (b * (d * e))) (- (b * (c * f))) (b * (d * f)))) ⟩
          a * (c * e) + ((- (a * (d * f))) + (((- (b * (d * e))) + (- (b * (c * f)))) + (b * (d * f))))
            ≡⟨ cong (λ t → a * (c * e) + ((- (a * (d * f))) + (t + (b * (d * f))))) (+-comm (- (b * (d * e))) (- (b * (c * f)))) ⟩
          a * (c * e) + ((- (a * (d * f))) + (((- (b * (c * f))) + (- (b * (d * e)))) + (b * (d * f))))
            ≡⟨ cong (λ t → a * (c * e) + t) (cong (λ t → (- (a * (d * f))) + t) (+-assoc (- (b * (c * f))) (- (b * (d * e))) (b * (d * f)))) ⟩
          a * (c * e) + ((- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + (b * (d * f)))))
            ≡⟨ sym (+-assoc (a * (c * e)) (- (a * (d * f))) ((- (b * (c * f))) + ((- (b * (d * e))) + (b * (d * f))))) ⟩
          a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
          ∎
        unfold1 : ∀ a b c d e f →
          a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
          ≡ a * (c * e - d * f) - b * (c * f + d * e - d * f)
        unfold1 a b c d e f = begin
          a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
            ≡⟨ cong (λ t → a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + t)))
                    (sym (neg-involutive (b * (d * f)))) ⟩
          a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + (- (- (b * (d * f))))))
            ≡⟨ cong (λ t → a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + t))
                    (sym (neg-distrib-+ (b * (d * e)) (- (b * (d * f))))) ⟩
          a * (c * e) + (- (a * (d * f))) + ((- (b * (c * f))) + (- ((b * (d * e)) + (- (b * (d * f))))))
            ≡⟨ cong (λ t → a * (c * e) + (- (a * (d * f))) + t)
                    (sym (neg-distrib-+ (b * (c * f)) ((b * (d * e)) + (- (b * (d * f)))))) ⟩
          a * (c * e) + (- (a * (d * f))) + (- (b * (c * f) + ((b * (d * e)) + (- (b * (d * f))))))
            ≡⟨ cong (λ t → t + (- (b * (c * f) + ((b * (d * e)) + (- (b * (d * f))))))) (a-fold a c d e f) ⟩
          a * (c * e - d * f) + (- (b * (c * f) + ((b * (d * e)) + (- (b * (d * f))))))
            ≡⟨ cong (λ t → a * (c * e - d * f) + (- t)) (b-fold b c d e f) ⟩
          a * (c * e - d * f) + (- (b * (c * f + d * e - d * f)))
            ≡⟨⟩
          a * (c * e - d * f) - b * (c * f + d * e - d * f)
          ∎ where
            a-fold : ∀ a c d e f →
              a * (c * e) + (- (a * (d * f))) ≡ a * (c * e - d * f)
            a-fold a c d e f = begin
              a * (c * e) + (- (a * (d * f)))
                ≡⟨ cong (λ t → a * (c * e) + t) (sym (neg-*-r a (d * f))) ⟩
              a * (c * e) + a * (- (d * f))
                ≡⟨ sym (*-distribˡ-+ a (c * e) (- (d * f))) ⟩
              a * (c * e - d * f)
              ∎
            b-fold : ∀ b c d e f →
              b * (c * f) + (b * (d * e) + (- (b * (d * f)))) ≡ b * (c * f + d * e - d * f)
            b-fold b c d e f = begin
              b * (c * f) + (b * (d * e) + (- (b * (d * f))))
                ≡⟨ sym (+-assoc (b * (c * f)) (b * (d * e)) (- (b * (d * f)))) ⟩
              (b * (c * f) + b * (d * e)) + (- (b * (d * f)))
                ≡⟨ cong (λ t → t + (- (b * (d * f)))) (sym (*-distribˡ-+ b (c * f) (d * e))) ⟩
              b * (c * f + d * e) + (- (b * (d * f)))
                ≡⟨ cong (λ t → b * (c * f + d * e) + t) (sym (neg-*-r b (d * f))) ⟩
              b * (c * f + d * e) + b * (- (d * f))
                ≡⟨ sym (*-distribˡ-+ b (c * f + d * e) (- (d * f))) ⟩
              b * ((c * f + d * e) + (- (d * f)))
                ≡⟨⟩
              b * (c * f + d * e - d * f)
              ∎
    comp2 : (a * c - b * d) * f + (a * d + b * c - b * d) * e - (a * d + b * c - b * d) * f
            ≡ a * (c * f + d * e - d * f) + b * (c * e - d * f) - b * (c * f + d * e - d * f)
    comp2 = begin
      (a * c - b * d) * f + (a * d + b * c - b * d) * e - (a * d + b * c - b * d) * f
        ≡⟨⟩
      (a * c + (- (b * d))) * f + ((a * d + b * c) + (- (b * d))) * e - ((a * d + b * c) + (- (b * d))) * f
        ≡⟨ cong₂ (λ x y → x + y - ((a * d + b * c) + (- (b * d))) * f)
                 (*-distribʳ-+ f (a * c) (- (b * d)))
                 (*-distribʳ-+ e (a * d + b * c) (- (b * d))) ⟩
      ((a * c) * f + (- (b * d)) * f) + (((a * d + b * c) * e) + ((- (b * d)) * e)) - ((a * d + b * c) + (- (b * d))) * f
        ≡⟨ cong₂ (λ x y → ((a * c) * f + x) + (((a * d + b * c) * e) + y) - ((a * d + b * c) + (- (b * d))) * f)
                 (neg-*-l (b * d) f)
                 (neg-*-l (b * d) e) ⟩
      ((a * c) * f + (- ((b * d) * f))) + (((a * d + b * c) * e) + (- ((b * d) * e))) - ((a * d + b * c) + (- (b * d))) * f
        ≡⟨ cong₂ (λ x y → ((a * c) * f + (- ((b * d) * f))) + (x + (- ((b * d) * e))) - y)
                 (*-distribʳ-+ e (a * d) (b * c))
                 (*-distribʳ-+ f (a * d + b * c) (- (b * d))) ⟩
      ((a * c) * f + (- ((b * d) * f))) + (((a * d) * e + (b * c) * e) + (- ((b * d) * e))) - (((a * d + b * c) * f) + ((- (b * d)) * f))
        ≡⟨ cong₂ (λ x y → ((a * c) * f + (- ((b * d) * f))) + (x + (- ((b * d) * e))) - (y + ((- (b * d)) * f)))
                 (cong₂ _+_ (*-assoc a d e) (*-assoc b c e))
                 (*-distribʳ-+ f (a * d) (b * c)) ⟩
      ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- ((b * d) * e))) - (((a * d) * f + (b * c) * f) + ((- (b * d)) * f))
        ≡⟨ cong₂ (λ x y → ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- x)) - (((a * d) * f + (b * c) * f) + y))
                 (*-assoc b d e)
                 refl ⟩
      ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - (((a * d) * f + (b * c) * f) + ((- (b * d)) * f))
        ≡⟨ cong (λ t → ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - (((a * d) * f + (b * c) * f) + t))
                 (neg-*-l (b * d) f) ⟩
      ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - (((a * d) * f + (b * c) * f) + (- ((b * d) * f)))
        ≡⟨ cong (λ t → ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - t)
                 (cong (λ t → (a * d) * f + (b * c) * f + t) (sym (+-identityˡ (- ((b * d) * f))))) ⟩
      ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * d) * f + (b * c) * f + (+0 - (b * d) * f))
        ≡⟨ cong (λ t → ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * d) * f + (b * c) * f + (+0 - t)))
                 (*-assoc b d f) ⟩
      ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * d) * f + (b * c) * f + (+0 - b * (d * f)))
        ≡⟨ cong (λ t → ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - t)
                 (cong (λ t → (a * d) * f + (b * c) * f + t) (+-identityˡ (- (b * (d * f))))) ⟩
      ((a * c) * f + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * d) * f + (b * c) * f + (- (b * (d * f))))
        ≡⟨ cong (λ t → (t + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * d) * f + (b * c) * f + (- (b * (d * f)))))
                 (*-assoc a c f) ⟩
      (a * (c * f) + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * d) * f + (b * c) * f + (- (b * (d * f))))
        ≡⟨ cong₂ (λ x y → (a * (c * f) + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((x + y) + (- (b * (d * f)))))
                 (*-assoc a d f)
                 (*-assoc b c f) ⟩
      (a * (c * f) + (- ((b * d) * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f))))
        ≡⟨ cong (λ t → (a * (c * f) + t) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f)))))
                 (sym (+-identityˡ (- ((b * d) * f)))) ⟩
      (a * (c * f) + (+0 - (b * d) * f)) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f))))
        ≡⟨ cong (λ t → (a * (c * f) + (+0 - t)) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f)))))
                 (*-assoc b d f) ⟩
      (a * (c * f) + (+0 - b * (d * f))) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f))))
        ≡⟨ cong (λ t → (a * (c * f) + t) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f)))))
                 (+-identityˡ (- (b * (d * f)))) ⟩
      (a * (c * f) - b * (d * f)) + ((a * (d * e) + b * (c * e)) + (- (b * (d * e)))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f))))
        ≡⟨ cong (λ t → (a * (c * f) + (- (b * (d * f)))) + t - ((a * (d * f) + b * (c * f)) + (- (b * (d * f)))))
                (+-assoc (a * (d * e)) (b * (c * e)) (- (b * (d * e)))) ⟩
      (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) - ((a * (d * f) + b * (c * f)) + (- (b * (d * f))))
        ≡⟨ cong (λ t → (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) - t)
                (+-assoc (a * (d * f)) (b * (c * f)) (- (b * (d * f)))) ⟩
      (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) - (a * (d * f) + (b * (c * f) + (- (b * (d * f)))))
        ≡⟨⟩
      (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + (- (a * (d * f) + (b * (c * f) + (- (b * (d * f))))))
        ≡⟨ cong (λ t → (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + t)
                (neg-distrib-+ (a * (d * f)) (b * (c * f) + (- (b * (d * f))))) ⟩
      (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + (- (b * (c * f) + (- (b * (d * f))))))
        ≡⟨ cong (λ t → (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + t))
                (neg-distrib-+ (b * (c * f)) (- (b * (d * f)))) ⟩
      (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + ((- (b * (c * f))) + (- (- (b * (d * f))))))
        ≡⟨ cong (λ t → (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + ((- (b * (c * f))) + t)))
                (neg-involutive (b * (d * f))) ⟩
      (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + ((- (b * (c * f))) + b * (d * f)))
        ≡⟨ canonical2-assoc a b c d e f ⟩
      (a * (c * f) + (a * (d * e) + (- (a * (d * f))))) + (b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f))))
        ≡⟨ cong₂ _+_ (fold2-a a c d e f) (fold2-b b c d e f) ⟩
      a * (c * f + d * e - d * f) + (b * (c * e - d * f) - b * (c * f + d * e - d * f))
        ≡⟨ sym (+-assoc (a * (c * f + d * e - d * f)) (b * (c * e - d * f)) (- (b * (c * f + d * e - d * f)))) ⟩
      a * (c * f + d * e - d * f) + b * (c * e - d * f) - b * (c * f + d * e - d * f)
      ∎ where


        shuffle4ℤ : ∀ A B C D → (A + B) + (C + D) ≡ (A + C) + (B + D)
        shuffle4ℤ A B C D = begin
          (A + B) + (C + D)
            ≡⟨ +-assoc A B (C + D) ⟩
          A + (B + (C + D))
            ≡⟨ cong (λ t → A + t) (sym (+-assoc B C D)) ⟩
          A + ((B + C) + D)
            ≡⟨ cong (λ t → A + (t + D)) (+-comm B C) ⟩
          A + ((C + B) + D)
            ≡⟨ cong (λ t → A + t) (+-assoc C B D) ⟩
          A + (C + (B + D))
            ≡⟨ sym (+-assoc A C (B + D)) ⟩
          (A + C) + (B + D)
          ∎
        canonical2-assoc : ∀ a b c d e f →
          (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + ((- (b * (c * f))) + b * (d * f)))
          ≡ (a * (c * f) + (a * (d * e) + (- (a * (d * f))))) + (b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f))))
        canonical2-assoc a b c d e f = begin
          (a * (c * f) + (- (b * (d * f)))) + (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + ((- (b * (c * f))) + b * (d * f)))
            ≡⟨ +-assoc (a * (c * f) + (- (b * (d * f)))) (a * (d * e) + (b * (c * e) + (- (b * (d * e))))) ((- (a * (d * f))) + ((- (b * (c * f))) + b * (d * f))) ⟩
          (a * (c * f) + (- (b * (d * f)))) + ((a * (d * e) + (b * (c * e) + (- (b * (d * e))))) + ((- (a * (d * f))) + ((- (b * (c * f))) + b * (d * f))))
            ≡⟨ cong (λ t → (a * (c * f) + (- (b * (d * f)))) + t) (shuffle4ℤ (a * (d * e)) (b * (c * e) + (- (b * (d * e)))) (- (a * (d * f))) ((- (b * (c * f))) + b * (d * f))) ⟩
          (a * (c * f) + (- (b * (d * f)))) + ((a * (d * e) + (- (a * (d * f)))) + ((b * (c * e) + (- (b * (d * e)))) + ((- (b * (c * f))) + b * (d * f))))
            ≡⟨ shuffle4ℤ (a * (c * f)) (- (b * (d * f))) (a * (d * e) + (- (a * (d * f)))) ((b * (c * e) + (- (b * (d * e)))) + ((- (b * (c * f))) + b * (d * f))) ⟩
          (a * (c * f) + (a * (d * e) + (- (a * (d * f))))) + ((- (b * (d * f))) + ((b * (c * e) + (- (b * (d * e)))) + ((- (b * (c * f))) + b * (d * f))))
            ≡⟨ cong (λ t → (a * (c * f) + (a * (d * e) + (- (a * (d * f))))) + t) (shuffle3-b b c d e f) ⟩
          (a * (c * f) + (a * (d * e) + (- (a * (d * f))))) + ((b * (c * e) + (- (b * (d * f)))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f))))
          ∎ where
            shuffle3-b : ∀ b c d e f →
              (- (b * (d * f))) + ((b * (c * e) + (- (b * (d * e)))) + ((- (b * (c * f))) + b * (d * f)))
              ≡ (b * (c * e) + (- (b * (d * f)))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
            shuffle3-b b c d e f = begin
              (- (b * (d * f))) + ((b * (c * e) + (- (b * (d * e)))) + ((- (b * (c * f))) + b * (d * f)))
                ≡⟨ cong (λ t → (- (b * (d * f))) + t)
                        (shuffle4ℤ (b * (c * e)) (- (b * (d * e))) (- (b * (c * f))) (b * (d * f))) ⟩
              (- (b * (d * f))) + ((b * (c * e) + (- (b * (c * f)))) + ((- (b * (d * e))) + b * (d * f)))
                ≡⟨ sym (+-assoc (- (b * (d * f))) (b * (c * e) + (- (b * (c * f)))) ((- (b * (d * e))) + b * (d * f))) ⟩
              ((- (b * (d * f))) + (b * (c * e) + (- (b * (c * f))))) + ((- (b * (d * e))) + b * (d * f))
                ≡⟨ cong (_+ ((- (b * (d * e))) + b * (d * f)))
                        (trans (sym (+-assoc (- (b * (d * f))) (b * (c * e)) (- (b * (c * f)))))
                               (cong (λ t → t + (- (b * (c * f)))) (+-comm (- (b * (d * f))) (b * (c * e))))) ⟩
              (b * (c * e) + (- (b * (d * f))) + (- (b * (c * f)))) + ((- (b * (d * e))) + b * (d * f))
                ≡⟨ +-assoc (b * (c * e) + (- (b * (d * f)))) (- (b * (c * f))) ((- (b * (d * e))) + b * (d * f)) ⟩
              (b * (c * e) + (- (b * (d * f)))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
              ∎
        fold2-a : ∀ a c d e f →
          a * (c * f) + (a * (d * e) + (- (a * (d * f)))) ≡ a * (c * f + d * e - d * f)
        fold2-a a c d e f = begin
          a * (c * f) + (a * (d * e) + (- (a * (d * f))))
            ≡⟨ sym (+-assoc (a * (c * f)) (a * (d * e)) (- (a * (d * f)))) ⟩
          (a * (c * f) + a * (d * e)) + (- (a * (d * f)))
            ≡⟨ cong (λ t → t + (- (a * (d * f)))) (sym (*-distribˡ-+ a (c * f) (d * e))) ⟩
          a * (c * f + d * e) + (- (a * (d * f)))
            ≡⟨ cong (λ t → a * (c * f + d * e) + t) (sym (neg-*-r a (d * f))) ⟩
          a * (c * f + d * e) + a * (- (d * f))
            ≡⟨ sym (*-distribˡ-+ a (c * f + d * e) (- (d * f))) ⟩
          a * ((c * f + d * e) + (- (d * f)))
            ≡⟨⟩
          a * (c * f + d * e - d * f)
          ∎
        fold2-b : ∀ b c d e f →
          b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
          ≡ b * (c * e - d * f) - b * (c * f + d * e - d * f)
        fold2-b b c d e f = begin
          b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + b * (d * f)))
            ≡⟨ cong (λ t → b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + t)))
                    (sym (neg-involutive (b * (d * f)))) ⟩
          b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + ((- (b * (d * e))) + (- (- (b * (d * f))))))
            ≡⟨ cong (λ t → b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + t))
                    (sym (neg-distrib-+ (b * (d * e)) (- (b * (d * f))))) ⟩
          b * (c * e) + (- (b * (d * f))) + ((- (b * (c * f))) + (- ((b * (d * e)) + (- (b * (d * f))))))
            ≡⟨ cong (λ t → b * (c * e) + (- (b * (d * f))) + t)
                    (sym (neg-distrib-+ (b * (c * f)) ((b * (d * e)) + (- (b * (d * f)))))) ⟩
          b * (c * e) + (- (b * (d * f))) + (- (b * (c * f) + ((b * (d * e)) + (- (b * (d * f))))))
            ≡⟨ cong₂ _+_ (fold2-first b c e d f) (cong -_ (fold2-b' b c d e f)) ⟩
          b * (c * e - d * f) + (- (b * (c * f + d * e - d * f)))
            ≡⟨⟩
          b * (c * e - d * f) - b * (c * f + d * e - d * f)
          ∎ where
            fold2-first : ∀ b c e d f →
              b * (c * e) + (- (b * (d * f))) ≡ b * (c * e - d * f)
            fold2-first b c e d f = begin
              b * (c * e) + (- (b * (d * f)))
                ≡⟨ cong (λ t → b * (c * e) + t) (sym (neg-*-r b (d * f))) ⟩
              b * (c * e) + b * (- (d * f))
                ≡⟨ sym (*-distribˡ-+ b (c * e) (- (d * f))) ⟩
              b * (c * e - d * f)
              ∎
            fold2-b' : ∀ b c d e f →
              b * (c * f) + (b * (d * e) + (- (b * (d * f)))) ≡ b * (c * f + d * e - d * f)
            fold2-b' b c d e f = begin
              b * (c * f) + (b * (d * e) + (- (b * (d * f))))
                ≡⟨ sym (+-assoc (b * (c * f)) (b * (d * e)) (- (b * (d * f)))) ⟩
              (b * (c * f) + b * (d * e)) + (- (b * (d * f)))
                ≡⟨ cong (λ t → t + (- (b * (d * f)))) (sym (*-distribˡ-+ b (c * f) (d * e))) ⟩
              b * (c * f + d * e) + (- (b * (d * f)))
                ≡⟨ cong (λ t → b * (c * f + d * e) + t) (sym (neg-*-r b (d * f))) ⟩
              b * (c * f + d * e) + b * (- (d * f))
                ≡⟨ sym (*-distribˡ-+ b (c * f + d * e) (- (d * f))) ⟩
              b * ((c * f + d * e) + (- (d * f)))
                ≡⟨⟩
              b * (c * f + d * e - d * f)
              ∎
-- (7) 乘法单位
*ᵉ-identityˡ : ∀ x → 1ᵉ *ᵉ x ≡ x
*ᵉ-identityˡ (eis a b) = cong₂ eis
  (trans (cong₂ _-_ (*-identityˡ a) (*-zeroˡ b)) (+-identityʳ a))
  (trans (cong₂ (λ x y → x + y - 0ℤ) (*-identityˡ b) (*-zeroˡ a))
         (trans (cong (_- 0ℤ) (+-identityʳ b)) (+-identityʳ b)))

*ᵉ-identityʳ : ∀ x → x *ᵉ 1ᵉ ≡ x
*ᵉ-identityʳ x = trans (*ᵉ-comm x 1ᵉ) (*ᵉ-identityˡ x)

-- (8) 分配律
*ᵉ-distribˡ : ∀ x y z → x *ᵉ (y +ᵉ z) ≡ (x *ᵉ y) +ᵉ (x *ᵉ z)
*ᵉ-distribˡ (eis a b) (eis c d) (eis e f) = cong₂ eis comp1 comp2
  where
    comp1 : a * (c + e) - b * (d + f) ≡ (a * c - b * d) + (a * e - b * f)
    comp1 = begin
      a * (c + e) - b * (d + f)
        ≡⟨ cong₂ _-_ (*-distribˡ-+ a c e) (*-distribˡ-+ b d f) ⟩
      (a * c + a * e) - (b * d + b * f)
        ≡⟨⟩
      (a * c + a * e) + (- (b * d + b * f))
        ≡⟨ cong (λ t → (a * c + a * e) + t) (neg-distrib-+ (b * d) (b * f)) ⟩
      (a * c + a * e) + ((- (b * d)) + (- (b * f)))
        ≡⟨ +-assoc (a * c) (a * e) ((- (b * d)) + (- (b * f))) ⟩
      a * c + (a * e + ((- (b * d)) + (- (b * f))))
        ≡⟨ cong (λ t → a * c + t) (sym (+-assoc (a * e) (- (b * d)) (- (b * f)))) ⟩
      a * c + ((a * e + (- (b * d))) + (- (b * f)))
        ≡⟨ cong (λ t → a * c + (t + (- (b * f)))) (+-comm (a * e) (- (b * d))) ⟩
      a * c + (((- (b * d)) + a * e) + (- (b * f)))
        ≡⟨ cong (λ t → a * c + t) (+-assoc (- (b * d)) (a * e) (- (b * f))) ⟩
      a * c + ((- (b * d)) + (a * e + (- (b * f))))
        ≡⟨ sym (+-assoc (a * c) (- (b * d)) (a * e + (- (b * f)))) ⟩
      (a * c + (- (b * d))) + (a * e + (- (b * f)))
        ≡⟨⟩
      (a * c - b * d) + (a * e - b * f)
      ∎
    comp2 : a * (d + f) + b * (c + e) - b * (d + f)
            ≡ (a * d + b * c - b * d) + (a * f + b * e - b * f)
    comp2 = begin
      a * (d + f) + b * (c + e) - b * (d + f)
        ≡⟨ cong₂ (λ x y → x + y - b * (d + f)) (*-distribˡ-+ a d f) (*-distribˡ-+ b c e) ⟩
      (a * d + a * f) + (b * c + b * e) - b * (d + f)
        ≡⟨ cong (λ t → (a * d + a * f) + (b * c + b * e) - t) (*-distribˡ-+ b d f) ⟩
      (a * d + a * f) + (b * c + b * e) - (b * d + b * f)
        ≡⟨⟩
      (a * d + a * f) + (b * c + b * e) + (- (b * d + b * f))
        ≡⟨ cong (λ t → (a * d + a * f) + (b * c + b * e) + t) (neg-distrib-+ (b * d) (b * f)) ⟩
      (a * d + a * f) + (b * c + b * e) + ((- (b * d)) + (- (b * f)))
        ≡⟨ canonical2 a d b c e f ⟩
      (a * d + b * c + (- (b * d))) + (a * f + b * e + (- (b * f)))
        ≡⟨⟩
      (a * d + b * c - b * d) + (a * f + b * e - b * f)
      ∎ where
        canonical2 : ∀ a d b c e f →
          (a * d + a * f) + (b * c + b * e) + ((- (b * d)) + (- (b * f)))
          ≡ (a * d + b * c + (- (b * d))) + (a * f + b * e + (- (b * f)))
        canonical2 a d b c e f = begin
          (a * d + a * f) + (b * c + b * e) + ((- (b * d)) + (- (b * f)))
            ≡⟨ cong (λ t → t + ((- (b * d)) + (- (b * f)))) (shuffle4ℤ' (a * d) (a * f) (b * c) (b * e)) ⟩
          (a * d + b * c) + (a * f + b * e) + ((- (b * d)) + (- (b * f)))
            ≡⟨ +-assoc (a * d + b * c) (a * f + b * e) ((- (b * d)) + (- (b * f))) ⟩
          (a * d + b * c) + ((a * f + b * e) + ((- (b * d)) + (- (b * f))))
            ≡⟨ cong (λ t → (a * d + b * c) + t) (sym (+-assoc (a * f + b * e) (- (b * d)) (- (b * f)))) ⟩
          (a * d + b * c) + (((a * f + b * e) + (- (b * d))) + (- (b * f)))
            ≡⟨ cong (λ t → (a * d + b * c) + (t + (- (b * f)))) (+-comm (a * f + b * e) (- (b * d))) ⟩
          (a * d + b * c) + (((- (b * d)) + (a * f + b * e)) + (- (b * f)))
            ≡⟨ cong (λ t → (a * d + b * c) + t) (+-assoc (- (b * d)) (a * f + b * e) (- (b * f))) ⟩
          (a * d + b * c) + ((- (b * d)) + ((a * f + b * e) + (- (b * f))))
            ≡⟨ sym (+-assoc (a * d + b * c) (- (b * d)) ((a * f + b * e) + (- (b * f)))) ⟩
          (a * d + b * c + (- (b * d))) + (a * f + b * e + (- (b * f)))
          ∎ where
            shuffle4ℤ' : ∀ A B C D → (A + B) + (C + D) ≡ (A + C) + (B + D)
            shuffle4ℤ' A B C D = begin
              (A + B) + (C + D)
                ≡⟨ +-assoc A B (C + D) ⟩
              A + (B + (C + D))
                ≡⟨ cong (λ t → A + t) (sym (+-assoc B C D)) ⟩
              A + ((B + C) + D)
                ≡⟨ cong (λ t → A + (t + D)) (+-comm B C) ⟩
              A + ((C + B) + D)
                ≡⟨ cong (λ t → A + t) (+-assoc C B D) ⟩
              A + (C + (B + D))
                ≡⟨ sym (+-assoc A C (B + D)) ⟩
              (A + C) + (B + D)
              ∎

*ᵉ-distribʳ : ∀ x y z → (x +ᵉ y) *ᵉ z ≡ (x *ᵉ z) +ᵉ (y *ᵉ z)
*ᵉ-distribʳ x y z = begin
  (x +ᵉ y) *ᵉ z
    ≡⟨ *ᵉ-comm (x +ᵉ y) z ⟩
  z *ᵉ (x +ᵉ y)
    ≡⟨ *ᵉ-distribˡ z x y ⟩
  (z *ᵉ x) +ᵉ (z *ᵉ y)
    ≡⟨ cong₂ _+ᵉ_ (*ᵉ-comm z x) (*ᵉ-comm z y) ⟩
  (x *ᵉ z) +ᵉ (y *ᵉ z)
  ∎

--------------------------------------------------------------------------------
-- 8. 范数 N(a+bω) = a² − ab + b², 乘性
--------------------------------------------------------------------------------

normᵉ : Eisenstein → ℤ
normᵉ (eis a b) = a * a - a * b + b * b

-- x · conj(x) = (N(x), 0)
norm-form : ∀ x → x *ᵉ conjᵉ x ≡ eis (normᵉ x) 0ℤ
norm-form (eis a b) = cong₂ eis comp1 comp2
  where
    comp1 : a * (a - b) - b * (0ℤ - b) ≡ a * a - a * b + b * b
    comp1 = begin
      a * (a - b) - b * (0ℤ - b)
        ≡⟨ cong₂ _-_ (*-distribˡ-+ a a (- b)) (*-distribˡ-+ b 0ℤ (- b)) ⟩
      (a * a + a * (- b)) - (b * 0ℤ + b * (- b))
        ≡⟨ cong₂ _-_ (cong (λ t → a * a + t) (neg-*-r a b))
                     (cong₂ _+_ (trans (*-comm b 0ℤ) (*-identityˡ 0ℤ)) (neg-*-r b b)) ⟩
      (a * a + (- (a * b))) - (0ℤ + (- (b * b)))
        ≡⟨ cong (λ t → (a * a + (- (a * b))) - t) (+-identityˡ (- (b * b))) ⟩
      (a * a + (- (a * b))) - (- (b * b))
        ≡⟨⟩
      (a * a + (- (a * b))) + (- (- (b * b)))
        ≡⟨ cong (λ t → (a * a + (- (a * b))) + t) (neg-involutive (b * b)) ⟩
      (a * a + (- (a * b))) + b * b
        ≡⟨⟩
      a * a - a * b + b * b
      ∎
    comp2 : a * (0ℤ - b) + b * (a - b) - b * (0ℤ - b) ≡ 0ℤ
    comp2 = begin
      a * (0ℤ - b) + b * (a - b) - b * (0ℤ - b)
        ≡⟨ cong₂ (λ x y → x + y - b * (0ℤ - b)) (*-distribˡ-+ a 0ℤ (- b)) (*-distribˡ-+ b a (- b)) ⟩
      (a * 0ℤ + a * (- b)) + (b * a + b * (- b)) - b * (0ℤ - b)
        ≡⟨ cong₂ (λ x y → (a * 0ℤ + x) + (b * a + y) - b * (0ℤ - b)) (neg-*-r a b) (neg-*-r b b) ⟩
      (a * 0ℤ + (- (a * b))) + (b * a + (- (b * b))) - b * (0ℤ - b)
        ≡⟨ cong (λ t → (a * 0ℤ + (- (a * b))) + (b * a + (- (b * b))) - t)
                (trans (*-distribˡ-+ b 0ℤ (- b)) (cong₂ _+_ (trans (*-comm b 0ℤ) (*-zeroˡ b)) (neg-*-r b b))) ⟩
      (a * 0ℤ + (- (a * b))) + (b * a + (- (b * b))) - (0ℤ + (- (b * b)))
        ≡⟨ cong (λ t → (t + (- (a * b))) + (b * a + (- (b * b))) - (0ℤ + (- (b * b)))) (trans (*-comm a 0ℤ) (*-zeroˡ a)) ⟩
      (0ℤ + (- (a * b))) + (b * a + (- (b * b))) - (0ℤ + (- (b * b)))
        ≡⟨ cong (λ t → (0ℤ + (- (a * b))) + (b * a + (- (b * b))) - t) (+-identityˡ (- (b * b))) ⟩
      (0ℤ + (- (a * b))) + (b * a + (- (b * b))) - (- (b * b))
        ≡⟨⟩
      (0ℤ + (- (a * b))) + (b * a + (- (b * b))) + (- (- (b * b)))
        ≡⟨ cong (λ t → (0ℤ + (- (a * b))) + (b * a + (- (b * b))) + t) (neg-involutive (b * b)) ⟩
      (0ℤ + (- (a * b))) + (b * a + (- (b * b))) + b * b
        ≡⟨ cong (λ t → t + (b * a + (- (b * b))) + b * b) (+-identityˡ (- (a * b))) ⟩
      (- (a * b)) + (b * a + (- (b * b))) + b * b
        ≡⟨ cong (λ t → (- (a * b)) + t + b * b) (cong (λ t → t + (- (b * b))) (*-comm b a)) ⟩
      (- (a * b)) + (a * b + (- (b * b))) + b * b
        ≡⟨ cong (λ t → t + b * b) (sym (+-assoc (- (a * b)) (a * b) (- (b * b)))) ⟩
      ((- (a * b)) + a * b) + (- (b * b)) + b * b
        ≡⟨ cong (λ t → t + (- (b * b)) + b * b) (+-comm (- (a * b)) (a * b)) ⟩
      (a * b + (- (a * b))) + (- (b * b)) + b * b
        ≡⟨ cong (λ t → t + (- (b * b)) + b * b) (+-inverseʳ (a * b)) ⟩
      0ℤ + (- (b * b)) + b * b
        ≡⟨ cong (λ t → t + b * b) (+-identityˡ (- (b * b))) ⟩
      (- (b * b)) + b * b
        ≡⟨ +-comm (- (b * b)) (b * b) ⟩
      b * b + (- (b * b))
        ≡⟨ +-inverseʳ (b * b) ⟩
      0ℤ
      ∎

-- 共轭乘法同态: conj(x·y) = conj(x)·conj(y)
conjᵉ-mul : ∀ x y → conjᵉ (x *ᵉ y) ≡ (conjᵉ x) *ᵉ (conjᵉ y)
conjᵉ-mul (eis a b) (eis c d) = cong₂ eis comp1 comp2
  where
    -- (-b)·(-d) = b·d (双负消去)
    neg-neg : (- b) * (- d) ≡ b * d
    neg-neg = begin
      (- b) * (- d)
        ≡⟨ neg-*-l b (- d) ⟩
      - (b * (- d))
        ≡⟨ cong -_ (neg-*-r b d) ⟩
      - (- (b * d))
        ≡⟨ neg-involutive (b * d) ⟩
      b * d
      ∎

    comp1 : (a * c - b * d) - (a * d + b * c - b * d)
            ≡ (a - b) * (c - d) - (0ℤ - b) * (0ℤ - d)
    comp1 = trans conj1-l (sym conj1-r)
      where
        conj1-l : (a * c - b * d) - (a * d + b * c - b * d)
                  ≡ a * c + ((- (a * d) + (- (b * c))) + (b * d + (- (b * d))))
        conj1-l = begin
          (a * c - b * d) - (a * d + b * c - b * d)
            ≡⟨⟩
          (a * c + (- (b * d))) + (- ((a * d + b * c) + (- (b * d))))
            ≡⟨ cong (λ t → (a * c + (- (b * d))) + t)
                    (neg-distrib-+ (a * d + b * c) (- (b * d))) ⟩
          (a * c + (- (b * d))) + ((- (a * d + b * c)) + (- (- (b * d))))
            ≡⟨ cong (λ t → (a * c + (- (b * d))) + (t + (- (- (b * d)))))
                    (neg-distrib-+ (a * d) (b * c)) ⟩
          (a * c + (- (b * d))) + ((- (a * d) + (- (b * c))) + (- (- (b * d))))
            ≡⟨ cong (λ t → (a * c + (- (b * d))) + ((- (a * d) + (- (b * c))) + t))
                    (neg-involutive (b * d)) ⟩
          (a * c + (- (b * d))) + ((- (a * d) + (- (b * c))) + b * d)
            ≡⟨ +-assoc (a * c) (- (b * d)) ((- (a * d) + (- (b * c))) + b * d) ⟩
          a * c + (- (b * d) + ((- (a * d) + (- (b * c))) + b * d))
            ≡⟨ cong (λ t → a * c + t)
                    (sym (+-assoc (- (b * d)) (- (a * d) + (- (b * c))) (b * d))) ⟩
          a * c + ((- (b * d) + (- (a * d) + (- (b * c)))) + b * d)
            ≡⟨ cong (λ t → a * c + (t + b * d))
                    (sym (+-assoc (- (b * d)) (- (a * d)) (- (b * c)))) ⟩
          a * c + (((- (b * d) + (- (a * d))) + (- (b * c))) + b * d)
            ≡⟨ cong (λ t → a * c + ((t + (- (b * c))) + b * d))
                    (+-comm (- (b * d)) (- (a * d))) ⟩
          a * c + (((- (a * d) + (- (b * d))) + (- (b * c))) + b * d)
            ≡⟨ cong (λ t → a * c + (t + b * d))
                    (+-assoc (- (a * d)) (- (b * d)) (- (b * c))) ⟩
          a * c + ((- (a * d) + (- (b * d) + (- (b * c)))) + b * d)
            ≡⟨ cong (λ t → a * c + ((- (a * d) + t) + b * d))
                    (+-comm (- (b * d)) (- (b * c))) ⟩
          a * c + ((- (a * d) + (- (b * c) + (- (b * d)))) + b * d)
            ≡⟨ cong (λ t → a * c + (t + b * d))
                    (sym (+-assoc (- (a * d)) (- (b * c)) (- (b * d)))) ⟩
          a * c + (((- (a * d) + (- (b * c))) + (- (b * d))) + b * d)
            ≡⟨ cong (λ t → a * c + t)
                    (+-assoc (- (a * d) + (- (b * c))) (- (b * d)) (b * d)) ⟩
          a * c + ((- (a * d) + (- (b * c))) + (- (b * d) + b * d))
            ≡⟨ cong (λ t → a * c + ((- (a * d) + (- (b * c))) + t))
                    (+-comm (- (b * d)) (b * d)) ⟩
          a * c + ((- (a * d) + (- (b * c))) + (b * d + (- (b * d))))
          ∎

        conj1-r : (a - b) * (c - d) - (0ℤ - b) * (0ℤ - d)
                  ≡ a * c + ((- (a * d) + (- (b * c))) + (b * d + (- (b * d))))
        conj1-r = begin
          (a - b) * (c - d) - (0ℤ - b) * (0ℤ - d)
            ≡⟨ cong (λ t → (a - b) * (c - d) - t)
                    (cong₂ _*_ (+-identityˡ (- b)) (+-identityˡ (- d))) ⟩
          (a - b) * (c - d) - (- b) * (- d)
            ≡⟨⟩
          (a - b) * (c - d) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → t + (- ((- b) * (- d))))
                    (*-distribʳ-+ (c - d) a (- b)) ⟩
          (a * (c - d) + (- b) * (c - d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (t + (- b) * (c - d)) + (- ((- b) * (- d))))
                    (*-distribˡ-+ a c (- d)) ⟩
          (a * c + a * (- d) + (- b) * (c - d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (a * c + t + (- b) * (c - d)) + (- ((- b) * (- d))))
                    (neg-*-r a d) ⟩
          (a * c + (- (a * d)) + (- b) * (c - d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (a * c + (- (a * d)) + t) + (- ((- b) * (- d))))
                    (*-distribˡ-+ (- b) c (- d)) ⟩
          (a * c + (- (a * d)) + ((- b) * c + (- b) * (- d))) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (a * c + (- (a * d)) + (t + (- b) * (- d))) + (- ((- b) * (- d))))
                    (neg-*-l b c) ⟩
          (a * c + (- (a * d)) + ((- (b * c)) + (- b) * (- d))) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (a * c + (- (a * d)) + ((- (b * c)) + t)) + (- ((- b) * (- d))))
                    (neg-neg) ⟩
          (a * c + (- (a * d)) + ((- (b * c)) + b * d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (a * c + (- (a * d)) + ((- (b * c)) + b * d)) + (- t))
                    (neg-neg) ⟩
          (a * c + (- (a * d)) + ((- (b * c)) + b * d)) + (- (b * d))
            ≡⟨ (+-assoc (a * c + (- (a * d))) ((- (b * c)) + b * d) (- (b * d))) ⟩
          (a * c + (- (a * d))) + ((- (b * c)) + b * d + (- (b * d)))
            ≡⟨ cong (λ t → (a * c + (- (a * d))) + t)
                    (+-assoc (- (b * c)) (b * d) (- (b * d))) ⟩
          (a * c + (- (a * d))) + (- (b * c) + (b * d + (- (b * d))))
            ≡⟨ (+-assoc (a * c) (- (a * d)) (- (b * c) + (b * d + (- (b * d))))) ⟩
          a * c + (- (a * d) + (- (b * c) + (b * d + (- (b * d)))))
            ≡⟨ cong (λ t → a * c + t)
                    (sym (+-assoc (- (a * d)) (- (b * c)) (b * d + (- (b * d))))) ⟩
          a * c + ((- (a * d) + (- (b * c))) + (b * d + (- (b * d))))
          ∎

    comp2 : 0ℤ - (a * d + b * c - b * d)
            ≡ (a - b) * (0ℤ - d) + (0ℤ - b) * (c - d) - (0ℤ - b) * (0ℤ - d)
    comp2 = trans conj2-l (sym conj2-r)
      where
        conj2-l : 0ℤ - (a * d + b * c - b * d)
                  ≡ 0ℤ + ((- (a * d) + (- (b * c))) + b * d)
        conj2-l = begin
          0ℤ - (a * d + b * c - b * d)
            ≡⟨⟩
          0ℤ + (- ((a * d + b * c) + (- (b * d))))
            ≡⟨ cong (λ t → 0ℤ + t) (neg-distrib-+ (a * d + b * c) (- (b * d))) ⟩
          0ℤ + ((- (a * d + b * c)) + (- (- (b * d))))
            ≡⟨ cong (λ t → 0ℤ + (t + (- (- (b * d))))) (neg-distrib-+ (a * d) (b * c)) ⟩
          0ℤ + ((- (a * d) + (- (b * c))) + (- (- (b * d))))
            ≡⟨ cong (λ t → 0ℤ + ((- (a * d) + (- (b * c))) + t)) (neg-involutive (b * d)) ⟩
          0ℤ + ((- (a * d) + (- (b * c))) + b * d)
          ∎

        conj2-r : (a - b) * (0ℤ - d) + (0ℤ - b) * (c - d) - (0ℤ - b) * (0ℤ - d)
                  ≡ 0ℤ + ((- (a * d) + (- (b * c))) + b * d)
        conj2-r = begin
          (a - b) * (0ℤ - d) + (0ℤ - b) * (c - d) - (0ℤ - b) * (0ℤ - d)
            ≡⟨ cong₂ (λ x y → x + y - (0ℤ - b) * (0ℤ - d))
                     (cong (λ t → (a - b) * t) (+-identityˡ (- d)))
                     (cong (λ t → t * (c - d)) (+-identityˡ (- b))) ⟩
          (a - b) * (- d) + (- b) * (c - d) - (0ℤ - b) * (0ℤ - d)
            ≡⟨ cong (λ t → (a - b) * (- d) + (- b) * (c - d) - t)
                    (cong₂ _*_ (+-identityˡ (- b)) (+-identityˡ (- d))) ⟩
          (a - b) * (- d) + (- b) * (c - d) - (- b) * (- d)
            ≡⟨⟩
          (a - b) * (- d) + (- b) * (c - d) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → t + (- b) * (c - d) + (- ((- b) * (- d))))
                    (*-distribʳ-+ (- d) a (- b)) ⟩
          (a * (- d) + (- b) * (- d)) + (- b) * (c - d) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (a * (- d) + (- b) * (- d)) + t + (- ((- b) * (- d))))
                    (*-distribˡ-+ (- b) c (- d)) ⟩
          (a * (- d) + (- b) * (- d)) + ((- b) * c + (- b) * (- d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (t + (- b) * (- d)) + ((- b) * c + (- b) * (- d)) + (- ((- b) * (- d))))
                    (neg-*-r a d) ⟩
          (- (a * d) + (- b) * (- d)) + ((- b) * c + (- b) * (- d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (- (a * d) + t) + ((- b) * c + (- b) * (- d)) + (- ((- b) * (- d))))
                    (neg-neg) ⟩
          (- (a * d) + b * d) + ((- b) * c + (- b) * (- d)) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (- (a * d) + b * d) + ((- b) * c + t) + (- ((- b) * (- d))))
                    (neg-neg) ⟩
          (- (a * d) + b * d) + ((- b) * c + b * d) + (- ((- b) * (- d)))
            ≡⟨ cong (λ t → (- (a * d) + b * d) + ((- b) * c + b * d) + (- t))
                    (neg-neg) ⟩
          (- (a * d) + b * d) + ((- b) * c + b * d) + (- (b * d))
            ≡⟨ cong (λ t → (- (a * d) + b * d) + (t + b * d) + (- (b * d)))
                    (neg-*-l b c) ⟩
          (- (a * d) + b * d) + ((- (b * c)) + b * d) + (- (b * d))
            ≡⟨ +-assoc (- (a * d) + b * d) ((- (b * c)) + b * d) (- (b * d)) ⟩
          (- (a * d) + b * d) + (((- (b * c)) + b * d) + (- (b * d)))
            ≡⟨ cong (λ t → (- (a * d) + b * d) + t)
                    (+-assoc (- (b * c)) (b * d) (- (b * d))) ⟩
          (- (a * d) + b * d) + (- (b * c) + (b * d + (- (b * d))))
            ≡⟨ cong (λ t → (- (a * d) + b * d) + (- (b * c) + t))
                    (+-inverseʳ (b * d)) ⟩
          (- (a * d) + b * d) + (- (b * c) + 0ℤ)
            ≡⟨ cong (λ t → (- (a * d) + b * d) + t)
                    (+-identityʳ (- (b * c))) ⟩
          (- (a * d) + b * d) + (- (b * c))
            ≡⟨ (+-assoc (- (a * d)) (b * d) (- (b * c))) ⟩
          - (a * d) + (b * d + (- (b * c)))
            ≡⟨ cong (λ t → - (a * d) + t) (+-comm (b * d) (- (b * c))) ⟩
          - (a * d) + (- (b * c) + b * d)
            ≡⟨ (sym (+-assoc (- (a * d)) (- (b * c)) (b * d))) ⟩
          (- (a * d) + (- (b * c))) + b * d
            ≡⟨ sym (+-identityˡ ((- (a * d) + (- (b * c))) + b * d)) ⟩
          0ℤ + ((- (a * d) + (- (b * c))) + b * d)
          ∎

-- 实轴嵌入乘法: (m,0)·(n,0) = (m·n, 0)
mul-real : ∀ m n → eis m 0ℤ *ᵉ eis n 0ℤ ≡ eis (m * n) 0ℤ
mul-real m n = cong₂ eis comp1 comp2
  where
    comp1 : m * n - 0ℤ * 0ℤ ≡ m * n
    comp1 = begin
      m * n - 0ℤ * 0ℤ
        ≡⟨ cong (λ t → m * n - t) (*-zeroˡ 0ℤ) ⟩
      m * n - 0ℤ
        ≡⟨ +-identityʳ (m * n) ⟩
      m * n
      ∎
    comp2 : m * 0ℤ + 0ℤ * n - 0ℤ * 0ℤ ≡ 0ℤ
    comp2 = begin
      m * 0ℤ + 0ℤ * n - 0ℤ * 0ℤ
        ≡⟨ cong₂ (λ x y → x + y - 0ℤ * 0ℤ) (*-zeroʳ m) (*-zeroˡ n) ⟩
      0ℤ + 0ℤ - 0ℤ * 0ℤ
        ≡⟨⟩
      0ℤ
      ∎

-- 范数乘性: N(x·y) = N(x)·N(y)
norm-mul : ∀ x y → normᵉ (x *ᵉ y) ≡ normᵉ x * normᵉ y
norm-mul x y = cong (λ e → Eisenstein.a e) chain
  where
    chain : eis (normᵉ (x *ᵉ y)) 0ℤ ≡ eis (normᵉ x * normᵉ y) 0ℤ
    chain = begin
      eis (normᵉ (x *ᵉ y)) 0ℤ
        ≡⟨ sym (norm-form (x *ᵉ y)) ⟩
      (x *ᵉ y) *ᵉ conjᵉ (x *ᵉ y)
        ≡⟨ cong (λ t → (x *ᵉ y) *ᵉ t) (conjᵉ-mul x y) ⟩
      (x *ᵉ y) *ᵉ (conjᵉ x *ᵉ conjᵉ y)
        ≡⟨ *ᵉ-assoc x y (conjᵉ x *ᵉ conjᵉ y) ⟩
      x *ᵉ (y *ᵉ (conjᵉ x *ᵉ conjᵉ y))
        ≡⟨ cong (λ t → x *ᵉ t) (sym (*ᵉ-assoc y (conjᵉ x) (conjᵉ y))) ⟩
      x *ᵉ ((y *ᵉ conjᵉ x) *ᵉ conjᵉ y)
        ≡⟨ cong (λ t → x *ᵉ (t *ᵉ conjᵉ y)) (*ᵉ-comm y (conjᵉ x)) ⟩
      x *ᵉ ((conjᵉ x *ᵉ y) *ᵉ conjᵉ y)
        ≡⟨ cong (λ t → x *ᵉ t) (*ᵉ-assoc (conjᵉ x) y (conjᵉ y)) ⟩
      x *ᵉ (conjᵉ x *ᵉ (y *ᵉ conjᵉ y))
        ≡⟨ sym (*ᵉ-assoc x (conjᵉ x) (y *ᵉ conjᵉ y)) ⟩
      (x *ᵉ conjᵉ x) *ᵉ (y *ᵉ conjᵉ y)
        ≡⟨ cong₂ _*ᵉ_ (norm-form x) (norm-form y) ⟩
      eis (normᵉ x) 0ℤ *ᵉ eis (normᵉ y) 0ℤ
        ≡⟨ mul-real (normᵉ x) (normᵉ y) ⟩
      eis (normᵉ x * normᵉ y) 0ℤ
      ∎

--------------------------------------------------------------------------------
-- 9. 6 个单位: {±1, ±ω, ±ω²}, 单位群 ≅ C₆
--------------------------------------------------------------------------------

unit1  : Eisenstein; unit1  = eis (+ 1) 0ℤ
unitm1 : Eisenstein; unitm1 = eis (-[1+ 0 ]) 0ℤ
unitω  : Eisenstein; unitω  = ωᵉ
unitω2 : Eisenstein; unitω2 = ω²ᵉ
unitmω : Eisenstein; unitmω = -ᵉ ωᵉ
unitmω2 : Eisenstein; unitmω2 = -ᵉ ω²ᵉ

-- 单位对 (互逆)
unit-inv-1   : unit1  *ᵉ unit1  ≡ 1ᵉ; unit-inv-1   = refl
unit-inv-m1  : unitm1 *ᵉ unitm1 ≡ 1ᵉ; unit-inv-m1  = refl
unit-inv-ω   : unitω  *ᵉ unitω2 ≡ 1ᵉ; unit-inv-ω   = refl
unit-inv-ω2  : unitω2 *ᵉ unitω  ≡ 1ᵉ; unit-inv-ω2  = refl
unit-inv-mω  : unitmω *ᵉ unitmω2 ≡ 1ᵉ; unit-inv-mω  = refl
unit-inv-mω2 : unitmω2 *ᵉ unitmω ≡ 1ᵉ; unit-inv-mω2 = refl

-- 单位范数均为 1
unit-norm-1   : normᵉ unit1  ≡ + 1; unit-norm-1   = refl
unit-norm-m1  : normᵉ unitm1 ≡ + 1; unit-norm-m1  = refl
unit-norm-ω   : normᵉ unitω  ≡ + 1; unit-norm-ω   = refl
unit-norm-ω2  : normᵉ unitω2 ≡ + 1; unit-norm-ω2  = refl
unit-norm-mω  : normᵉ unitmω ≡ + 1; unit-norm-mω  = refl
unit-norm-mω2 : normᵉ unitmω2 ≡ + 1; unit-norm-mω2 = refl

-- 单位群 ≅ C₆: 生成元 g = 1+ω = −ω²
unitGen : Eisenstein
unitGen = eis (+ 1) (+ 1)

-- g⁰..g⁶ 遍历 6 个单位并回到 1 (g = 1+ω = −ω²)
--   1 → 1+ω → ω → −1 → ω² → −ω → 1
unitGen-pow-0 : 1ᵉ ≡ unit1;            unitGen-pow-0 = refl
unitGen-pow-1 : unitGen ≡ unitmω2;      unitGen-pow-1 = refl
unitGen-pow-2 : unitGen *ᵉ unitGen ≡ unitω;  unitGen-pow-2 = refl
unitGen-pow-3 : (unitGen *ᵉ unitGen) *ᵉ unitGen ≡ unitm1; unitGen-pow-3 = refl
unitGen-pow-4 : ((unitGen *ᵉ unitGen) *ᵉ unitGen) *ᵉ unitGen ≡ unitω2; unitGen-pow-4 = refl
unitGen-pow-5 : (((unitGen *ᵉ unitGen) *ᵉ unitGen) *ᵉ unitGen) *ᵉ unitGen ≡ unitmω; unitGen-pow-5 = refl
unitGen-pow-6 : ((((unitGen *ᵉ unitGen) *ᵉ unitGen) *ᵉ unitGen) *ᵉ unitGen) *ᵉ unitGen ≡ unit1; unitGen-pow-6 = refl
