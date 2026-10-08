{-# OPTIONS --cubical --guardedness #-}
module Sovereign.Algebra.BurauCubical where

-- | Sovereign.Algebra.BurauCubical
--
-- Burau 表示 B₃ → Mat3(ℤ[t,t⁻¹]) 的函数表示（裸系数函数版，沿 LaurentCubical
-- 「逐点相等避 funExt 类型推断问题」先例——Mat3 系数取 ℤ→ℤ，IsFinSupp 不进矩阵层）。
--
-- 数学背景：
--   Burau 表示 σᵢ ↦ I_{i-1} ⊕ [[1-t, t],[1, 0]] ⊕ I_{n-i-1}
--   B₃ 生成元（3×3 块嵌入）：
--     σ₁ = [[1,0,0],[0,1-t,t],[0,1,0]]
--     σ₂ = [[1-t,t,0],[1,0,0],[0,0,1]]
--   braid 关系 σ₁σ₂σ₁ = σ₂σ₁σ₂（oracle 已核 t∈[-6,6]，engineering/burau_oracle.py）
--   2×2 变体经 oracle 裁定不满足 braid，弃用（台账 Burau.B3GL2.Mat2 形式化修正记录）

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Int.Properties using (+Assoc; +Comm; ·DistR+; ·DistL+; ·Assoc; ·Comm)



-- 9 项纯重排：列分组 → 行分组（三明治交换法，21 步）
-- 三明治：p+(q+r) ≡ q+(p+r)
open import Cubical.Data.Int using (ℤ; _+_; _-_; _·_; pos; negsuc; sucℤ; predℤ; _+pos_; _+negsuc_)


open import Cubical.Foundations.Prelude using (_≡_; refl; sym; cong; cong₂; _∙_; funExt)
assocP : ∀ x y z → x + (y + z) ≡ (x + y) + z
assocP x y (pos z) = +Assoc x y (pos z)
assocP x y (negsuc z) = +Assoc x y (negsuc z)



swap3 : ∀ p q r → p + (q + r) ≡ q + (p + r)
swap3 p q r = +Assoc p q r ∙ cong (_+ r) (+Comm p q) ∙ sym (+Assoc q p r)

interchange : ∀ (a b c d : ℤ) → (a + b) + (c + d) ≡ (a + c) + (b + d)
interchange a b c d =
  let s1 : (a + b) + (c + d) ≡ ((a + b) + c) + d
      s1 = +Assoc (a + b) c d
      s2 : ((a + b) + c) + d ≡ (a + (b + c)) + d
      s2 = cong (λ w → w + d) (sym (+Assoc a b c))
      s3a : (a + (b + c)) + d ≡ a + ((b + c) + d)
      s3a = sym (+Assoc a (b + c) d)
      s3b : a + ((b + c) + d) ≡ a + ((c + b) + d)
      s3b = cong (λ w → a + (w + d)) (+Comm b c)
      s4a : a + ((c + b) + d) ≡ (a + (c + b)) + d
      s4a = +Assoc a (c + b) d
      s4b : (a + (c + b)) + d ≡ ((a + c) + b) + d
      s4b = cong (λ w → w + d) (assocP a c b)
      s4c : (((a + c) + b)) + d ≡ (a + c) + (b + d)
      s4c = sym (+Assoc (a + c) b d)
  in s1 ∙ s2 ∙ s3a ∙ s3b ∙ s4a ∙ s4b ∙ s4c
c5-lem : ∀ (v1 v4 v7 v2 v5 v8 v3 v6 v9 : ℤ) →
  ((v1 + v4) + v7) + ((v2 + v5) + (v8 + (v3 + (v6 + v9)))) ≡ ((v1 + v4) + v7) + ((v2 + v5) + ((v8 + ((v3 + v6)) + v9)))
c5-lem v1 v4 v7 v2 v5 v8 v3 v6 v9 =
  let m1 : v3 + (v6 + v9) ≡ (v3 + v6) + v9
      m1 = +Assoc v3 v6 v9
      W = (v3 + v6) + v9
      X1 = ((v1 + v4) + v7) + ((v2 + v5) + (v8 + (v3 + (v6 + v9))))
      X2 = ((v1 + v4) + v7) + ((v2 + v5) + (v8 + W))
      q1 : X1 ≡ X2
      q1 = cong (λ w → ((v1 + v4) + v7) + ((v2 + v5) + (v8 + w))) m1
      q2 : X2 ≡ ((v1 + v4) + v7) + ((v2 + v5) + ((v8 + ((v3 + v6)) + v9)))
      q2 = cong (λ w → ((v1 + v4) + v7) + ((v2 + v5) + w)) (+Assoc v8 ((v3 + v6)) v9)
  in q1 ∙ q2

c6-lem : ∀ (v1 v4 v7 v2 v5 v8 v3 v6 v9 : ℤ) →
  ((v1 + v4) + v7) + ((v2 + v5) + (v8 + ((v3 + v6) + v9))) ≡ (((v1 + v4) + v7) + (((v2 + v5) + ((v8 + ((v3 + v6)) + v9)))))
c6-lem v1 v4 v7 v2 v5 v8 v3 v6 v9 =
  let m1 : v8 + ((v3 + v6) + v9) ≡ (v8 + (v3 + v6)) + v9
      m1 = assocP v8 (v3 + v6) v9
      S = ((v1 + v4) + v7) + ((v2 + v5))
      X1 = S + (v8 + ((v3 + v6) + v9))
      X2 = S + ((v8 + ((v3 + v6)) + v9))
      p1 : X1 ≡ X2
      p1 = cong (λ w → S + w) m1
      m2c : (v2 + v5) + (v8 + ((v3 + v6) + v9)) ≡ ((v2 + v5) + v8) + ((v3 + v6) + v9)
      m2c = +Assoc (v2 + v5) v8 ((v3 + v6) + v9)
      X3 = S + (((v2 + v5) + v8) + ((v3 + v6) + v9))
      p2 : X2 ≡ X3
      p2 = cong (λ w → S + w) m2c
      p3 : X3 ≡ (((v1 + v4) + v7) + (((v2 + v5) + v8) + (((v3 + v6)) + v9)))
      p3 = cong (λ w → ((v1 + v4) + v7) + w) (+Assoc (v2 + v5) v8 ((v3 + v6) + v9))
      m2c : (v2 + v5) + (v8 + ((v3 + v6) + v9)) ≡ ((v2 + v5) + v8) + ((v3 + v6) + v9)
      m2c = +Assoc (v2 + v5) v8 ((v3 + v6) + v9)
      X3 = ((v1 + v4) + v7) + ((((v2 + v5) + v8)) + (((v3 + v6)) + v9))
      p3 : X3 ≡ (((v1 + v4) + v7) + (((v2 + v5) + v8) + (((v3 + v6)) + v9)))
      p3 = cong (λ w → ((v1 + v4) + v7) + w) m2c
  in p1 ∙ p2 ∙ p3
-- ────────────────────────────────────────────────────────────────────
-- 系数函数常量：0、1、t、1-t（按 ℤ 构造子分派）
-- ────────────────────────────────────────────────────────────────────

cf0 : ℤ → ℤ
cf0 _ = pos zero

cf1 : ℤ → ℤ
cf1 (pos zero) = pos (suc zero)
cf1 (pos (suc n)) = pos zero
cf1 (negsuc n) = pos zero

cft : ℤ → ℤ
cft (pos (suc zero)) = pos (suc zero)
cft (pos zero) = pos zero
cft (pos (suc (suc n))) = pos zero
cft (negsuc n) = pos zero

cfo : ℤ → ℤ
cfo (pos zero) = pos (suc zero)
cfo (pos (suc zero)) = negsuc zero
cfo (pos (suc (suc n))) = pos zero
cfo (negsuc n) = pos zero

-- ────────────────────────────────────────────────────────────────────
-- 3×3 矩阵：record 9 系数函数（行主序）
-- ────────────────────────────────────────────────────────────────────

record Mat3 : Set where
  constructor mat3
  field
    a11 a12 a13 a21 a22 a23 a31 a32 a33 : ℤ → ℤ

id3 : Mat3
id3 = mat3 cf1 cf0 cf0
           cf0 cf1 cf0
           cf0 cf0 cf1

-- 矩阵乘法：c_ij = Σ_k a_ik * b_kj（Int 算术，加法结合序 (x+y)+z）
_*3_ : Mat3 → Mat3 → Mat3
(mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33) *3 (mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33) =
  mat3
    (λ n → ((a11 n · b11 n) + (a12 n · b21 n)) + (a13 n · b31 n))
    (λ n → ((a11 n · b12 n) + (a12 n · b22 n)) + (a13 n · b32 n))
    (λ n → ((a11 n · b13 n) + (a12 n · b23 n)) + (a13 n · b33 n))
    (λ n → ((a21 n · b11 n) + (a22 n · b21 n)) + (a23 n · b31 n))
    (λ n → ((a21 n · b12 n) + (a22 n · b22 n)) + (a23 n · b32 n))
    (λ n → ((a21 n · b13 n) + (a22 n · b23 n)) + (a23 n · b33 n))
    (λ n → ((a31 n · b11 n) + (a32 n · b21 n)) + (a33 n · b31 n))
    (λ n → ((a31 n · b12 n) + (a32 n · b22 n)) + (a33 n · b32 n))
    (λ n → ((a31 n · b13 n) + (a32 n · b23 n)) + (a33 n · b33 n))

-- ────────────────────────────────────────────────────────────────────
-- Burau 生成元（标准 B₃ 块嵌入）
-- ────────────────────────────────────────────────────────────────────

burau-s1 : Mat3
burau-s1 = mat3 cf1 cf0 cf0
                cf0 cfo cft
                cf0 cf1 cf0

burau-s2 : Mat3
burau-s2 = mat3 cfo cft cf0
                cf1 cf0 cf0
                cf0 cf0 cf1


-- ────────────────────────────────────────────────────────────────────
-- braid 关系：σ₁σ₂σ₁ = σ₂σ₁σ₂（逐 entry funExt，4-case refl）
-- oracle 预核：engineering/burau_oracle.py（t∈[-6,6]）
-- ────────────────────────────────────────────────────────────────────

private
  e11 : Mat3.a11 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a11 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e11 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e12 : Mat3.a12 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a12 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e12 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e13 : Mat3.a13 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a13 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e13 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e21 : Mat3.a21 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a21 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e21 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e22 : Mat3.a22 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a22 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e22 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e23 : Mat3.a23 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a23 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e23 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e31 : Mat3.a31 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a31 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e31 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e32 : Mat3.a32 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a32 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e32 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

  e33 : Mat3.a33 ((burau-s1 *3 burau-s2) *3 burau-s1) ≡ Mat3.a33 ((burau-s2 *3 burau-s1) *3 burau-s2)
  e33 = funExt λ { (pos zero) → refl ; (pos (suc zero)) → refl ; (pos (suc (suc n))) → refl ; (negsuc n) → refl }

-- record 构造子级 9 field 相等组合（9 段单参 cong 链）
mat3-cong : ∀ {a11 a12 a13 a21 a22 a23 a31 a32 a33 b11 b12 b13 b21 b22 b23 b31 b32 b33}
  → a11 ≡ b11 → a12 ≡ b12 → a13 ≡ b13
  → a21 ≡ b21 → a22 ≡ b22 → a23 ≡ b23
  → a31 ≡ b31 → a32 ≡ b32 → a33 ≡ b33
  → mat3 a11 a12 a13 a21 a22 a23 a31 a32 a33 ≡ mat3 b11 b12 b13 b21 b22 b23 b31 b32 b33
mat3-cong {a11} {a12} {a13} {a21} {a22} {a23} {a31} {a32} {a33} {b11} {b12} {b13} {b21} {b22} {b23} {b31} {b32} {b33} p1 p2 p3 p4 p5 p6 p7 p8 p9 =
      cong (λ z → mat3 z a12 a13 a21 a22 a23 a31 a32 a33) p1
  ∙ cong (λ z → mat3 b11 z a13 a21 a22 a23 a31 a32 a33) p2
  ∙ cong (λ z → mat3 b11 b12 z a21 a22 a23 a31 a32 a33) p3
  ∙ cong (λ z → mat3 b11 b12 b13 z a22 a23 a31 a32 a33) p4
  ∙ cong (λ z → mat3 b11 b12 b13 b21 z a23 a31 a32 a33) p5
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 z a31 a32 a33) p6
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 b23 z a32 a33) p7
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 b23 b31 z a33) p8
  ∙ cong (λ z → mat3 b11 b12 b13 b21 b22 b23 b31 b32 z) p9

braid-rel : (burau-s1 *3 burau-s2) *3 burau-s1 ≡ (burau-s2 *3 burau-s1) *3 burau-s2
braid-rel = mat3-cong e11 e12 e13 e21 e22 e23 e31 e32 e33

-- ────────────────────────────────────────────────────────────────────
-- 通用 entry 结合引理（矩阵乘法结合律的纯 Int 内核，9 项重排）
-- LHS：(g1·c1 + g2·c2) + g3·c3，g_i = (a₁·b_1i + a₂·b_2i) + a₃·b_3i
-- RHS：(a₁·Q1 + a₂·Q2) + a₃·Q3，Q_i = (b_1i·c1 + b_2i·c2) + b_3i·c3
-- ────────────────────────────────────────────────────────────────────

assoc-entry : ∀ a₁ a₂ a₃ b11 b12 b13 b21 b22 b23 b31 b32 b33 c1 c2 c3 n →
    ((((a₁ n · b11 n) + (a₂ n · b21 n)) + (a₃ n · b31 n)) · c1 n
    + (((a₁ n · b12 n) + (a₂ n · b22 n)) + (a₃ n · b32 n)) · c2 n)
    + (((a₁ n · b13 n) + (a₂ n · b23 n)) + (a₃ n · b33 n)) · c3 n
    ≡
    ((a₁ n · ((b11 n · c1 n) + (b12 n · c2 n) + (b13 n · c3 n)))
    + (a₂ n · ((b21 n · c1 n) + (b22 n · c2 n) + (b23 n · c3 n))))
    + (a₃ n · ((b31 n · c1 n) + (b32 n · c2 n) + (b33 n · c3 n)))
assoc-entry a₁ a₂ a₃ b11 b12 b13 b21 b22 b23 b31 b32 b33 c1 c2 c3 n =
  {!main-chain!}

row-col : ∀ v1 v2 v3 v4 v5 v6 v7 v8 v9 →
      (((v1 + v2) + v3) + ((v4 + v5) + v6)) + ((v7 + v8) + v9)
  ≡   (((v1 + v4) + v7) + ((v2 + v5) + v8)) + ((v3 + v6) + v9)
row-col v1 v2 v3 v4 v5 v6 v7 v8 v9 =
      let Y = (v4 + (v5 + v6))
          Z = (v7 + (v8 + v9))
          U = ((v1 + v4) + v7) + ((v2 + v5))
          -- 展开 4 步（三组列 → 右结合 col 序）
          e1 : ((v1 + (v2 + v3)) + (Y + Z)) ≡ (v1 + ((v2 + v3) + (Y + Z)))
          e1 = sym (+Assoc v1 (v2 + v3) (Y + Z))
          e2 : (v1 + ((v2 + v3) + (Y + Z))) ≡ (v1 + (v2 + (v3 + (Y + Z))))
          e2 = cong (v1 +_) (sym (+Assoc v2 v3 (Y + Z)))
          e3 : (v1 + (v2 + (v3 + (Y + Z)))) ≡ (v1 + (v2 + (v3 + (v4 + ((v5 + v6) + Z)))))
          e3 = cong (λ w → v1 + (v2 + (v3 + w))) (sym (+Assoc v4 (v5 + v6) Z))
          e4 : (v1 + (v2 + (v3 + (v4 + ((v5 + v6) + Z))))) ≡ (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + Z))))))
          e4 = cong (λ w → v1 + (v2 + (v3 + (v4 + w)))) (sym (+Assoc v5 v6 Z))
          b1 : (v1 + (v2 + (v3 + (v4 + (v5 + (v6 + (v7 + (v8 + v9)))))))) ≡ (v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + v9))))))))
          b1 = cong (λ w → v1 + (v2 + w)) (swap3 v3 v4 (v5 + (v6 + (v7 + (v8 + v9)))))
          b2 : (v1 + (v2 + (v4 + (v3 + (v5 + (v6 + (v7 + (v8 + v9)))))))) ≡ (v1 + (v2 + (v4 + (v5 + (v3 + (v6 + (v7 + (v8 + v9))))))))
          b2 = cong (λ w → v1 + (v2 + (v4 + w))) (swap3 v3 v5 (v6 + (v7 + (v8 + v9))))
          b3 : (v1 + (v2 + (v4 + (v5 + (v3 + (v6 + (v7 + (v8 + v9)))))))) ≡ (v1 + (v4 + (v2 + (v5 + (v3 + (v6 + (v7 + (v8 + v9))))))))
          b3 = cong (v1 +_) (swap3 v2 v4 (v5 + (v3 + (v6 + (v7 + (v8 + v9))))))
          b4 : (v1 + (v4 + (v2 + (v5 + (v3 + (v6 + (v7 + (v8 + v9)))))))) ≡ (v1 + (v4 + (v2 + (v5 + (v3 + (v7 + (v6 + (v8 + v9))))))))
          b4 = cong (λ w → v1 + (v4 + (v2 + (v5 + (v3 + w))))) (swap3 v6 v7 (v8 + v9))
          b5 : (v1 + (v4 + (v2 + (v5 + (v3 + (v7 + (v6 + v9))))))) ≡ (v1 + (v4 + (v2 + (v5 + (v7 + (v3 + (v6 + v9)))))))
          b5 = cong (λ w → v1 + (v4 + (v2 + (v5 + w)))) (swap3 v3 v7 (v6 + v9))
          b6 : (v1 + (v4 + (v2 + (v5 + (v7 + (v3 + (v6 + v9))))))) ≡ (v1 + (v4 + (v2 + (v7 + (v5 + (v3 + (v6 + v9)))))))
          b6 = cong (λ w → v1 + (v4 + (v2 + w))) (swap3 v5 v7 (v3 + (v6 + v9)))
          b7 : (v1 + (v4 + (v2 + (v7 + (v5 + (v3 + (v6 + (v8 + v9)))))))) ≡ (v1 + (v4 + (v2 + (v7 + (v5 + (v3 + (v8 + (v6 + v9))))))))
          b7 = cong (λ w → v1 + (v4 + (v2 + (v7 + (v5 + (v3 + w)))))) (swap3 v6 v8 v9)
          b8 : (v1 + (v4 + (v2 + (v7 + (v5 + (v3 + (v8 + (v6 + v9)))))))) ≡ (v1 + (v4 + (v2 + (v7 + (v5 + (v8 + (v3 + (v6 + v9))))))))
          b8 = cong (λ w → v1 + (v4 + (v2 + (v7 + (v5 + w))))) (swap3 v3 v8 (v6 + v9))
          c1 : (v1 + (v4 + (v2 + (v7 + (v5 + (v3 + (v8 + (v6 + v9)))))))) ≡ ((v1 + v4) + (v2 + (v7 + (v5 + (v3 + (v8 + (v6 + v9)))))))
          c1 = +Assoc v1 v4 (v2 + (v7 + (v5 + (v3 + (v8 + (v6 + v9))))))
          c2 : ((v1 + v4) + (v2 + (v7 + (v5 + (v3 + (v8 + (v6 + v9))))))) ≡ ((v1 + v4) + (v7 + ((v2 + v5) + (v3 + (v8 + (v6 + v9))))))
          c2 = cong (λ w → (v1 + v4) + w) (swap3 v2 v7 (v5 + (v3 + (v8 + (v6 + v9)))) ∙ cong (λ w2 → v7 + w2) (+Assoc v2 v5 (v3 + (v8 + (v6 + v9)))))
          c3 : ((v1 + v4) + (v7 + ((v2 + v5) + (v3 + (v8 + (v6 + v9)))))) ≡  (((v1 + v4) + v7) + ((v2 + v5) + (v3 + (v8 + (v6 + v9)))))
          c3 = +Assoc (v1 + v4) v7 ((v2 + v5) + (v3 + (v8 + (v6 + v9))))
          c4 : (((v1 + v4) + v7) + ((v2 + v5) + (v3 + (v8 + (v6 + v9))))) ≡ (((v1 + v4) + v7) + ((v2 + v5) + ((v8 + (v3 + (v6 + v9))))))
          c4 = cong (λ w → U + w) (swap3 v3 v8 (v6 + v9))
          c5 : (((v1 + v4) + v7) + ((v2 + v5) + ((v8 + (v3 + (v6 + v9)))))) ≡ (((v1 + v4) + v7) + ((v2 + v5) + ((v8 + ((v3 + v6)) + v9))))
          c5 = c5-lem v1 v4 v7 v2 v5 v8 v3 v6 v9
          c6 : (((v1 + v4) + v7) + ((v2 + v5) + ((v8 + ((v3 + v6)) + v9)))) ≡ (((v1 + v4) + v7) + ((((v2 + v5) + v8)) + ((v3 + v6) + v9)))
          c6 = c6-lem v1 v4 v7 v2 v5 v8 v3 v6 v9
          c7 = c6
      in e1 ∙ e2 ∙ e3 ∙ e4 ∙ b1 ∙ b2 ∙ b3 ∙ b4 ∙ b5 ∙ b6 ∙ b7 ∙ c1 ∙ c2 ∙ c3 ∙ c4 ∙ c5 ∙ c6




