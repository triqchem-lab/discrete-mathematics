{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.A4.SpinNoInvariantLine
--
-- **2 维旋量的不变线障碍**（第二块：Z[ω] 无挠 + 系数事实 + 四个分量化简 + 两条线性方程）
--
-- 上一文件 `SpinIrreducible` 证到：不变线 ⇒ ρ(g0) 与 ρ(g9) 在公共特征向量 v 上交换。
-- 本文件把"交换"落成两条具体线性方程：
--
--     (E1) ω²·y ≡ y ⊕ (−1)·x
--     (E2) (−ω)·x ⊕ (−1)·y ≡ (−1)·x
--
-- 需要的三样东西：
--   ① Z[ω] 无挠（`two-zero`）—— 库内原先没有，本文件补；
--   ② 加法换位 / 右消去（`add-swap`、`add-cancelʳ`）；
--   ③ 复合作用的**系数事实**（ω·ω = ω²、ω³ = 1、ω·(1+ω) = −1、(1+ω)·ω² = −ω、…）。
--      ⚠ 这些**不能**用 refl：ℤ 的 `_*_` 由 `sign ◃ (|_| * |_|)` 定义，含负数的乘积
--      不按字面归约。故用 `Data.Integer.Properties` 的 `neg-distribˡ-*` /
--      `neg-distrib-+` / `neg-involutive` 逐坐标化简。
--
-- 消元（2·x ≡ 0、2·y ≡ 0）与最终矛盾在下一文件；本文件做到 E1、E2。
--
-- 0 postulate / 0 hole。
module Sovereign.Synthesis.A4.SpinNoInvariantLine where

open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; _*_; -_)
open import Data.Integer.Properties using (neg-distribʳ-*; neg-involutive)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; zeroZω; oneZω; negZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using ( addZω-assoc; addZω-comm; addZω-identityˡ; addZω-identityʳ
        ; addZω-inverseʳ
        ; mulZω-assoc; mulZω-distribʳ; mulZω-distribˡ; mulZω-identityˡ
        ; mulZω-zeroˡ )

open import Sovereign.Synthesis.A4.BilinearSchur2A4
  using (M2E; m2e; mulME; toME; c0; c1; cm1; cw; cw2; c1w; cmw)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep using (g0; g9)
open import Sovereign.Synthesis.A4.SpinIrreducible
  using (Pair; zeroV; mulMV; scaleV; commute-on-eigenvector)

--------------------------------------------------------------------------------
-- ① Z[ω] 无挠：2·z ≡ 0 ⇒ z ≡ 0
--------------------------------------------------------------------------------

twoZ : Zω
twoZ = mkZω (+ 2) (+ 0)

dbl-zero-ℤ : ∀ (m : ℤ) → m + m ≡ (+ 0) → m ≡ (+ 0)
dbl-zero-ℤ (+ zero)    _ = refl
dbl-zero-ℤ (+ (suc n)) ()
dbl-zero-ℤ (-[1+ n ])  ()

self-zero : ∀ (z : Zω) → addZω z z ≡ zeroZω → z ≡ zeroZω
self-zero (mkZω a b) h =
  cong₂ mkZω (dbl-zero-ℤ a (cong Zω.a h)) (dbl-zero-ℤ b (cong Zω.b h))

twoZ-mul : ∀ (z : Zω) → mulZω twoZ z ≡ addZω z z
twoZ-mul z =
  trans (mulZω-distribʳ oneZω oneZω z)
        (cong₂ addZω (mulZω-identityˡ z) (mulZω-identityˡ z))

two-zero : ∀ (z : Zω) → mulZω twoZ z ≡ zeroZω → z ≡ zeroZω
two-zero z h = self-zero z (trans (sym (twoZ-mul z)) h)

--------------------------------------------------------------------------------
-- ② 加法换位与右消去
--------------------------------------------------------------------------------

-- | (a ⊕ b) ⊕ c ≡ (a ⊕ c) ⊕ b
add-swap : ∀ (a b c : Zω) → addZω (addZω a b) c ≡ addZω (addZω a c) b
add-swap a b c = begin
    addZω (addZω a b) c
  ≡⟨ addZω-assoc a b c ⟩
    addZω a (addZω b c)
  ≡⟨ cong (addZω a) (addZω-comm b c) ⟩
    addZω a (addZω c b)
  ≡⟨ sym (addZω-assoc a c b) ⟩
    addZω (addZω a c) b ∎

-- | 右消去：p ⊕ r ≡ q ⊕ r ⇒ p ≡ q
add-cancelʳ : ∀ (p q r : Zω) → addZω p r ≡ addZω q r → p ≡ q
add-cancelʳ p q r h = begin
    p
  ≡⟨ sym (addZω-identityʳ p) ⟩
    addZω p zeroZω
  ≡⟨ cong (addZω p) (sym (addZω-inverseʳ r)) ⟩
    addZω p (addZω r (negZω r))
  ≡⟨ sym (addZω-assoc p r (negZω r)) ⟩
    addZω (addZω p r) (negZω r)
  ≡⟨ cong (λ t → addZω t (negZω r)) h ⟩
    addZω (addZω q r) (negZω r)
  ≡⟨ addZω-assoc q r (negZω r) ⟩
    addZω q (addZω r (negZω r))
  ≡⟨ cong (addZω q) (addZω-inverseʳ r) ⟩
    addZω q zeroZω
  ≡⟨ addZω-identityʳ q ⟩
    q ∎

--------------------------------------------------------------------------------
-- ③ 系数事实（逐坐标，用 ℤ 的 negation 分配律化简）
--
--   记 ω = cw = (0,1)，ω² = cw2 = (−1,−1)，1 = c1，−1 = cm1 = (−1,0)，
--   1+ω = c1w = (1,1)，−ω = cmw = (0,−1)。
--------------------------------------------------------------------------------

-- | ω·0 ≡ 0
cw-c0 : mulZω cw c0 ≡ zeroZω
cw-c0 = refl

-- | ω·ω ≡ ω²
cw-cw : mulZω cw cw ≡ cw2
cw-cw = refl

-- | ω²·ω ≡ 1（ω³ = 1）
cw2-cw : mulZω cw2 cw ≡ c1
cw2-cw = refl

-- | ω·(1+ω) ≡ −1
cw-c1w : mulZω cw c1w ≡ cm1
cw-c1w = refl

-- | (1+ω)·ω² ≡ −ω（⚠ 非 refl：含负数乘积，需 ℤ 的 negation 分配律）
c1w-cw2 : mulZω c1w cw2 ≡ cmw
c1w-cw2 = cong₂ mkZω q1 q2
  where
    -- 坐标 1：1·(−1) − 1·(−1) ≡ 0
    q1 : (+ 1) * (-[1+ 0 ]) - (+ 1) * (-[1+ 0 ]) ≡ (+ 0)
    q1 = begin
        (+ 1) * (-[1+ 0 ]) - (+ 1) * (-[1+ 0 ])
      ≡⟨ cong₂ _-_
           (trans (sym (neg-distribʳ-* (+ 1) (+ 1))) refl)
           (trans (sym (neg-distribʳ-* (+ 1) (+ 1))) refl) ⟩
        - ((+ 1) * (+ 1)) - (- ((+ 1) * (+ 1)))
      ≡⟨ refl ⟩
        (+ 0)
      ∎
    -- 坐标 2：1·(−1) + 1·(−1) − 1·(−1) ≡ −1
    q2 : (+ 1) * (-[1+ 0 ]) + (+ 1) * (-[1+ 0 ]) - (+ 1) * (-[1+ 0 ]) ≡ -[1+ 0 ]
    q2 = begin
        (+ 1) * (-[1+ 0 ]) + (+ 1) * (-[1+ 0 ]) - (+ 1) * (-[1+ 0 ])
      ≡⟨ cong₂ (λ u v → u + v - (+ 1) * (-[1+ 0 ]))
           (trans (sym (neg-distribʳ-* (+ 1) (+ 1))) refl)
           (trans (sym (neg-distribʳ-* (+ 1) (+ 1))) refl) ⟩
        - ((+ 1) * (+ 1)) + (- ((+ 1) * (+ 1))) - (+ 1) * (-[1+ 0 ])
      ≡⟨ cong (λ t → - ((+ 1) * (+ 1)) + (- ((+ 1) * (+ 1))) - t)
              (trans (sym (neg-distribʳ-* (+ 1) (+ 1))) refl) ⟩
        - ((+ 1) * (+ 1)) + (- ((+ 1) * (+ 1))) - (- ((+ 1) * (+ 1)))
      ≡⟨ refl ⟩
        -[1+ 0 ]
      ∎

-- | (1+ω)·ω ≡ −1
c1w-cw : mulZω c1w cw ≡ cm1
c1w-cw = refl

--------------------------------------------------------------------------------
-- ④ 矩阵乘法与矩阵-向量作用相容：ρ(A·B)·v ≡ ρ(A)·(ρ(B)·v)
--
--   这条把"复合作用"换成"复合矩阵的作用"，从而可以把 ρ(g0)·ρ(g9) 这类
--   **闭矩阵**先算成一个具体矩阵，再作用到 v 上（否则闭系数会让 Agda 一路
--   归约到 ℤ 坐标层，符号化的化简步骤无法展开。
--
--   系数全部为变量，故所有步骤都是结构性的（distrib / assoc / 4 项换位）。
--------------------------------------------------------------------------------

-- | 四项换位：(A ⊕ B) ⊕ (C ⊕ D) ≡ (A ⊕ C) ⊕ (B ⊕ D)
add-swap4 : ∀ (a b c d : Zω)
          → addZω (addZω a b) (addZω c d) ≡ addZω (addZω a c) (addZω b d)
add-swap4 a b c d = begin
    addZω (addZω a b) (addZω c d)
  ≡⟨ addZω-assoc a b (addZω c d) ⟩
    addZω a (addZω b (addZω c d))
  ≡⟨ cong (addZω a) (sym (addZω-assoc b c d)) ⟩
    addZω a (addZω (addZω b c) d)
  ≡⟨ cong (λ t → addZω a (addZω t d)) (addZω-comm b c) ⟩
    addZω a (addZω (addZω c b) d)
  ≡⟨ cong (addZω a) (addZω-assoc c b d) ⟩
    addZω a (addZω c (addZω b d))
  ≡⟨ sym (addZω-assoc a c (addZω b d)) ⟩
    addZω (addZω a c) (addZω b d) ∎

-- | 一行：(ae ⊕ bg)·x ⊕ (af ⊕ bh)·y ≡ a·(ex ⊕ fy) ⊕ b·(gx ⊕ hy)
row-mix : ∀ (a b e f g h x y : Zω)
        → addZω (mulZω (addZω (mulZω a e) (mulZω b g)) x)
                 (mulZω (addZω (mulZω a f) (mulZω b h)) y)
        ≡ addZω (mulZω a (addZω (mulZω e x) (mulZω f y)))
                (mulZω b (addZω (mulZω g x) (mulZω h y)))
row-mix a b e f g h x y = begin
    addZω (mulZω (addZω (mulZω a e) (mulZω b g)) x)
          (mulZω (addZω (mulZω a f) (mulZω b h)) y)
  ≡⟨ cong₂ addZω (mulZω-distribʳ (mulZω a e) (mulZω b g) x)
                  (mulZω-distribʳ (mulZω a f) (mulZω b h) y) ⟩
    addZω (addZω (mulZω (mulZω a e) x) (mulZω (mulZω b g) x))
          (addZω (mulZω (mulZω a f) y) (mulZω (mulZω b h) y))
  ≡⟨ add-swap4 (mulZω (mulZω a e) x) (mulZω (mulZω b g) x)
               (mulZω (mulZω a f) y) (mulZω (mulZω b h) y) ⟩
    addZω (addZω (mulZω (mulZω a e) x) (mulZω (mulZω a f) y))
          (addZω (mulZω (mulZω b g) x) (mulZω (mulZω b h) y))
  ≡⟨ cong₂ addZω
        (cong₂ addZω (mulZω-assoc a e x) (mulZω-assoc a f y))
        (cong₂ addZω (mulZω-assoc b g x) (mulZω-assoc b h y)) ⟩
    addZω (addZω (mulZω a (mulZω e x)) (mulZω a (mulZω f y)))
          (addZω (mulZω b (mulZω g x)) (mulZω b (mulZω h y)))
  ≡⟨ cong₂ addZω
        (sym (mulZω-distribˡ a (mulZω e x) (mulZω f y)))
        (sym (mulZω-distribˡ b (mulZω g x) (mulZω h y))) ⟩
    addZω (mulZω a (addZω (mulZω e x) (mulZω f y)))
          (mulZω b (addZω (mulZω g x) (mulZω h y))) ∎

-- | 矩阵乘法与作用相容：ρ(A·B)·v ≡ ρ(A)·(ρ(B)·v)
mulMV-mulME : ∀ (A B : M2E) (v : Pair) → mulMV (mulME A B) v ≡ mulMV A (mulMV B v)
mulMV-mulME (m2e a b c d) (m2e e f g h) (x , y) =
  cong₂ _,_ (row-mix a b e f g h x y) (row-mix c d e f g h x y)
