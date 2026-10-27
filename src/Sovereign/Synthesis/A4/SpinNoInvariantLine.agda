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
open import Data.Integer.Properties using (neg-distribˡ-*; neg-distribʳ-*; neg-involutive; +-inverseˡ; +-inverseʳ)
open import Data.Nat using (zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; module ≡-Reasoning)

open ≡-Reasoning

open import Sovereign.Synthesis.A4.A4Representation
  using (Zω; mkZω; zeroZω; oneZω; negZω; addZω; mulZω)
open import Sovereign.Algebra.FieldTower.Zomega
  using ( addZω-assoc; addZω-comm; addZω-identityˡ; addZω-identityʳ
        ; addZω-inverseʳ
        ; add-swap; add-swap4
        ; mulZω-assoc; mulZω-distribʳ; mulZω-distribˡ; mulZω-identityˡ
        ; mulZω-zeroˡ; mulZω-zeroʳ )

open import Sovereign.Synthesis.A4.BilinearSchur2A4
  using (M2E; m2e; mulME; toME; c0; c1; cm1; cw; cw2; c1w; cmw)
open import Sovereign.Synthesis.A4.BinaryTetrahedralDefiningRep using (SL23; g0; g9)
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

fourZ : Zω
fourZ = mkZω (+ 4) (+ 0)

-- | 2·2 ≡ 4（闭的正数乘积，refl 级）
fourZ-mul : mulZω twoZ twoZ ≡ fourZ
fourZ-mul = refl

-- | 4·z ≡ 0 ⇒ z ≡ 0（两次 two-zero；3 维的 det = 4 子式要用）
four-zero : ∀ (z : Zω) → mulZω fourZ z ≡ zeroZω → z ≡ zeroZω
four-zero z h =
  two-zero z
    (two-zero (mulZω twoZ z)
      (trans (sym (trans (cong (λ t → mulZω t z) (sym fourZ-mul))
                         (mulZω-assoc twoZ twoZ z))) h))

-- | (−1) ⊕ 1 ≡ 0（ℤ 的对加逆）
cm1-plus-c1 : addZω cm1 c1 ≡ zeroZω
cm1-plus-c1 = cong₂ mkZω (+-inverseˡ (+ 1)) refl

-- | 1 ⊕ (−1) ≡ 0
c1-plus-cm1 : addZω c1 cm1 ≡ zeroZω
c1-plus-cm1 = cong₂ mkZω (+-inverseʳ (+ 1)) refl

--------------------------------------------------------------------------------
-- ② 加法换位与右消去
--------------------------------------------------------------------------------

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
--   4 项换位 `add-swap4` 与 3 项换位 `add-swap` 是纯加法事实，已上提到
--   `Sov.Algebra.FieldTower.Zomega` §1.5（3 维路同用）。
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- ⑤ 两个闭乘积矩阵与四个分量化简
--
--   ρ(g0) = [[0, ω], [1+ω, 0]]，ρ(g9) = [[ω², ω], [0, ω]]
--   ρ(g0)·ρ(g9) = [[0, ω²], [−ω, −1]]      ρ(g9)·ρ(g0) = [[−1, 1], [−1, 0]]
--   （数值已复核；每个条目都只用 ④ 里已证的系数事实 + 零元/单位律）
--------------------------------------------------------------------------------

-- | 0·x ⊕ b ≡ b（单 cong，避免 cong₂ + refl 的隐式参数歧义）
addZω-zero-mulˡ : ∀ (x b : Zω) → addZω (mulZω c0 x) b ≡ b
addZω-zero-mulˡ x b =
  trans (cong (λ t → addZω t b) (mulZω-zeroˡ x)) (addZω-identityˡ b)

-- | a ⊕ 0·y ≡ a
addZω-mul-zeroʳ : ∀ (a y : Zω) → addZω a (mulZω c0 y) ≡ a
addZω-mul-zeroʳ a y =
  trans (cong (addZω a) (mulZω-zeroˡ y)) (addZω-identityʳ a)

m2e-cong : ∀ {a b c d a' b' c' d' : Zω}
         → a ≡ a' → b ≡ b' → c ≡ c' → d ≡ d' → m2e a b c d ≡ m2e a' b' c' d'
m2e-cong refl refl refl refl = refl

AB-mat : mulME (toME g0) (toME g9) ≡ m2e c0 cw2 cmw cm1
AB-mat = m2e-cong
  (trans (cong₂ addZω (mulZω-zeroˡ cw2) cw-c0) (addZω-identityˡ zeroZω))
  (trans (cong₂ addZω (mulZω-zeroˡ cw) cw-cw) (addZω-identityˡ cw2))
  (trans (cong₂ addZω c1w-cw2 (mulZω-zeroˡ c0)) (addZω-identityʳ cmw))
  (trans (cong₂ addZω c1w-cw (mulZω-zeroˡ cw)) (addZω-identityʳ cm1))

BA-mat : mulME (toME g9) (toME g0) ≡ m2e cm1 c1 cm1 c0
BA-mat = m2e-cong
  (trans (cong₂ addZω (mulZω-zeroʳ cw2) cw-c1w) (addZω-identityˡ cm1))
  (trans (cong₂ addZω cw2-cw cw-c0) (addZω-identityʳ c1))
  (trans (cong₂ addZω (mulZω-zeroˡ c0) cw-c1w) (addZω-identityˡ cm1))
  (trans (cong₂ addZω (mulZω-zeroˡ cw) cw-c0) (addZω-identityˡ zeroZω))

-- | A(Bv)₁ ≡ ω²·y
ABv-fst : ∀ (x y : Zω)
        → proj₁ (mulMV (toME g0) (mulMV (toME g9) (x , y))) ≡ mulZω cw2 y
ABv-fst x y =
  trans (cong proj₁ (sym (mulMV-mulME (toME g0) (toME g9) (x , y))))
    (trans (cong (λ M → proj₁ (mulMV M (x , y))) AB-mat)
      (addZω-zero-mulˡ x (mulZω cw2 y)))

-- | B(Av)₁ ≡ y ⊕ (−1)·x
BAv-fst : ∀ (x y : Zω)
        → proj₁ (mulMV (toME g9) (mulMV (toME g0) (x , y)))
        ≡ addZω y (mulZω cm1 x)
BAv-fst x y =
  trans (cong proj₁ (sym (mulMV-mulME (toME g9) (toME g0) (x , y))))
    (trans (cong (λ M → proj₁ (mulMV M (x , y))) BA-mat)
      (trans (cong (addZω (mulZω cm1 x)) (mulZω-identityˡ y))
             (addZω-comm (mulZω cm1 x) y)))

-- | A(Bv)₂ ≡ (−ω)·x ⊕ (−1)·y
ABv-snd : ∀ (x y : Zω)
        → proj₂ (mulMV (toME g0) (mulMV (toME g9) (x , y)))
        ≡ addZω (mulZω cmw x) (mulZω cm1 y)
ABv-snd x y =
  trans (cong proj₂ (sym (mulMV-mulME (toME g0) (toME g9) (x , y))))
    (cong (λ M → proj₂ (mulMV M (x , y))) AB-mat)

-- | B(Av)₂ ≡ (−1)·x
BAv-snd : ∀ (x y : Zω)
        → proj₂ (mulMV (toME g9) (mulMV (toME g0) (x , y))) ≡ mulZω cm1 x
BAv-snd x y =
  trans (cong proj₂ (sym (mulMV-mulME (toME g9) (toME g0) (x , y))))
    (trans (cong (λ M → proj₂ (mulMV M (x , y))) BA-mat)
      (addZω-mul-zeroʳ (mulZω cm1 x) y))

--------------------------------------------------------------------------------
-- ⑥ 两条线性方程
--------------------------------------------------------------------------------

E1 : ∀ (x y c d : Zω)
   → mulMV (toME g0) (x , y) ≡ scaleV c (x , y)
   → mulMV (toME g9) (x , y) ≡ scaleV d (x , y)
   → mulZω cw2 y ≡ addZω y (mulZω cm1 x)
E1 x y c d Av Bv =
  trans (sym (ABv-fst x y))
    (trans (cong proj₁ (commute-on-eigenvector (toME g0) (toME g9) (x , y) c d Av Bv))
           (BAv-fst x y))

E2 : ∀ (x y c d : Zω)
   → mulMV (toME g0) (x , y) ≡ scaleV c (x , y)
   → mulMV (toME g9) (x , y) ≡ scaleV d (x , y)
   → addZω (mulZω cmw x) (mulZω cm1 y) ≡ mulZω cm1 x
E2 x y c d Av Bv =
  trans (sym (ABv-snd x y))
    (trans (cong proj₂ (commute-on-eigenvector (toME g0) (toME g9) (x , y) c d Av Bv))
           (BAv-snd x y))

--------------------------------------------------------------------------------
-- ⑦ 消元：由 E1、E2 得 2·y ≡ 0、2·x ≡ 0
--
--   记 A = 1−ω、B = ω²−1、D = (−1)·B（= 1−ω²）。三步：
--     (i)  E2 两边加 (1·x)      ⇒ A·x ⊕ (−1)·y ≡ 0
--     (ii) E1 两边加 (−1)·y     ⇒ B·y ≡ (−1)·x
--     (iii) (ii) 乘 (−1)        ⇒ D·y ≡ x
--   把 (iii) 代入 (i)：A·D·y ⊕ (−1)·y ≡ 0，而 A·D = 3
--     ⇒ (3 + (−1))·y ≡ 2·y ≡ 0 ⇒ `two-zero` 得 y = 0；
--   再由 (iii) 得 x = 0。
--------------------------------------------------------------------------------

A₁ B₁ D₁ threeZ : Zω
A₁ = addZω cmw c1            -- 1 − ω
B₁ = addZω cw2 cm1           -- ω² − 1
D₁ = mulZω cm1 B₁            -- 1 − ω²
threeZ = mkZω (+ 3) (+ 0)

-- ℤ 层：负数乘法的两个方向（把 stdlib 的 neg-distrib* 转成"乘负数"形态）
neg-mulˡ-ℤ : ∀ (i j : ℤ) → (- i) * j ≡ - (i * j)
neg-mulˡ-ℤ i j = sym (neg-distribˡ-* i j)

neg-mulʳ-ℤ : ∀ (i j : ℤ) → i * (- j) ≡ - (i * j)
neg-mulʳ-ℤ i j = sym (neg-distribʳ-* i j)

-- 具体的负数乘积事实（各三/四步，末项是字面量故可归约）
neg1-neg1 : (- (+ 1)) * (- (+ 1)) ≡ (+ 1)
neg1-neg1 =
  trans (neg-mulˡ-ℤ (+ 1) (- (+ 1)))
    (trans (cong -_ (neg-mulʳ-ℤ (+ 1) (+ 1))) (neg-involutive ((+ 1) * (+ 1))))

neg1-neg2 : (- (+ 1)) * (- (+ 2)) ≡ (+ 2)
neg1-neg2 =
  trans (neg-mulˡ-ℤ (+ 1) (- (+ 2)))
    (trans (cong -_ (neg-mulʳ-ℤ (+ 1) (+ 2))) (neg-involutive ((+ 1) * (+ 2))))

neg1-pos1 : (- (+ 1)) * (+ 1) ≡ (- (+ 1))
neg1-pos1 = neg-mulˡ-ℤ (+ 1) (+ 1)

neg1-pos2 : (- (+ 1)) * (+ 2) ≡ (- (+ 2))
neg1-pos2 = neg-mulˡ-ℤ (+ 1) (+ 2)

-- | (−1)·(−1) ≡ 1
cm1-cm1 : mulZω cm1 cm1 ≡ c1
cm1-cm1 = cong₂ mkZω
  (trans (cong (λ t → t - (+ 0) * (+ 0)) neg1-neg1) refl)
  refl

-- | D₁ = 1−ω² 的坐标：(−1,0)·(−2,−1) = (2,1)
D₁-val : D₁ ≡ mkZω (+ 2) (+ 1)
D₁-val = cong₂ mkZω
  (trans (cong (λ t → t - (+ 0) * (-[1+ 0 ])) neg1-neg2) refl)
  (trans (cong (λ t → t + (+ 0) * (-[1+ 1 ]) - (+ 0) * (-[1+ 0 ])) neg1-neg1) refl)

-- | A₁·D₁ ≡ 3（A₁ = (1,−1)，D₁ = (2,1)）
AD-three : mulZω A₁ D₁ ≡ threeZ
AD-three = trans (cong (mulZω A₁) D₁-val)
  (cong₂ mkZω
    (trans (cong (λ v → (+ 1) * (+ 2) - v) neg1-pos1) refl)
    (trans (cong (λ v → (+ 1) * (+ 1) + v - (- (+ 1)) * (+ 1)) neg1-pos2)
           (trans (cong (λ v → (+ 1) * (+ 1) + (- (+ 2)) - v) neg1-pos1) refl)))

-- | 3 + (−1) ≡ 2
three-plus-cm1 : addZω threeZ cm1 ≡ twoZ
three-plus-cm1 = refl

-- | (i) A₁·x ⊕ (−1)·y ≡ 0（把 E2 的 x 系数补成 1−ω）
shift-E2 : ∀ (x y : Zω)
         → addZω (mulZω cmw x) (mulZω cm1 y) ≡ mulZω cm1 x
         → addZω (mulZω A₁ x) (mulZω cm1 y) ≡ zeroZω
shift-E2 x y E2h = trans (sym L2) (trans (sym L1) (trans E2' (trans R1 R2)))
  where
    E2' : addZω (addZω (mulZω cmw x) (mulZω cm1 y)) (mulZω c1 x)
        ≡ addZω (mulZω cm1 x) (mulZω c1 x)
    E2' = cong (λ t → addZω t (mulZω c1 x)) E2h

    L1 : addZω (addZω (mulZω cmw x) (mulZω cm1 y)) (mulZω c1 x)
       ≡ addZω (addZω (mulZω cmw x) (mulZω c1 x)) (mulZω cm1 y)
    L1 = add-swap (mulZω cmw x) (mulZω cm1 y) (mulZω c1 x)

    L2 : addZω (addZω (mulZω cmw x) (mulZω c1 x)) (mulZω cm1 y)
       ≡ addZω (mulZω A₁ x) (mulZω cm1 y)
    L2 = cong (λ t → addZω t (mulZω cm1 y)) (sym (mulZω-distribʳ cmw c1 x))

    R1 : addZω (mulZω cm1 x) (mulZω c1 x) ≡ mulZω (addZω cm1 c1) x
    R1 = sym (mulZω-distribʳ cm1 c1 x)

    R2 : mulZω (addZω cm1 c1) x ≡ zeroZω
    R2 = trans (cong (λ t → mulZω t x) cm1-plus-c1) (mulZω-zeroˡ x)

-- | (ii) B₁·y ≡ (−1)·x（把 E1 的 y 系数补成 ω²−1）
shift-E1 : ∀ (x y : Zω)
         → mulZω cw2 y ≡ addZω y (mulZω cm1 x)
         → mulZω B₁ y ≡ mulZω cm1 x
shift-E1 x y E1h = trans (sym M1) (trans E1' M3)
  where
    E1' : addZω (mulZω cw2 y) (mulZω cm1 y)
        ≡ addZω (addZω y (mulZω cm1 x)) (mulZω cm1 y)
    E1' = cong (λ t → addZω t (mulZω cm1 y)) E1h

    M1 : addZω (mulZω cw2 y) (mulZω cm1 y) ≡ mulZω B₁ y
    M1 = sym (mulZω-distribʳ cw2 cm1 y)

    M2a : addZω y (mulZω cm1 y) ≡ zeroZω
    M2a = trans (cong (λ t → addZω t (mulZω cm1 y)) (sym (mulZω-identityˡ y)))
                (trans (sym (mulZω-distribʳ c1 cm1 y))
                       (trans (cong (λ t → mulZω t y) c1-plus-cm1)
                              (mulZω-zeroˡ y)))

    M3 : addZω (addZω y (mulZω cm1 x)) (mulZω cm1 y) ≡ mulZω cm1 x
    M3 = trans (add-swap y (mulZω cm1 x) (mulZω cm1 y))
               (trans (cong (λ t → addZω t (mulZω cm1 x)) M2a)
                      (addZω-identityˡ (mulZω cm1 x)))

-- | (iii) D₁·y ≡ x（把 (ii) 两边乘 (−1)）
x-from-y : ∀ (x y : Zω)
         → mulZω B₁ y ≡ mulZω cm1 x
         → mulZω D₁ y ≡ x
x-from-y x y h = trans (sym L) (trans (cong (mulZω cm1) h) R)
  where
    L : mulZω cm1 (mulZω B₁ y) ≡ mulZω D₁ y
    L = sym (mulZω-assoc cm1 B₁ y)

    R : mulZω cm1 (mulZω cm1 x) ≡ x
    R = trans (sym (mulZω-assoc cm1 cm1 x))
              (trans (cong (λ t → mulZω t x) cm1-cm1) (mulZω-identityˡ x))

-- | **2·y ≡ 0**
two-y : ∀ (x y : Zω)
      → addZω (mulZω cmw x) (mulZω cm1 y) ≡ mulZω cm1 x
      → mulZω cw2 y ≡ addZω y (mulZω cm1 x)
      → mulZω twoZ y ≡ zeroZω
two-y x y E2h E1h =
  trans (sym s5)
    (trans (mulZω-distribʳ threeZ cm1 y)
      (trans (sym s3)
        (trans (cong (λ t → addZω t (mulZω cm1 y)) (mulZω-assoc A₁ D₁ y))
          (trans (cong (λ t → addZω (mulZω A₁ t) (mulZω cm1 y))
                       (x-from-y x y (shift-E1 x y E1h)))
                 (shift-E2 x y E2h)))))
  where
    s5 : mulZω twoZ y ≡ mulZω (addZω threeZ cm1) y
    s5 = cong (λ t → mulZω t y) three-plus-cm1

    s3 : addZω (mulZω (mulZω A₁ D₁) y) (mulZω cm1 y)
       ≡ addZω (mulZω threeZ y) (mulZω cm1 y)
    s3 = cong (λ t → addZω (mulZω t y) (mulZω cm1 y)) AD-three

-- | **2·x ≡ 0**
two-x : ∀ (x y : Zω)
      → mulZω B₁ y ≡ mulZω cm1 x
      → y ≡ zeroZω
      → mulZω twoZ x ≡ zeroZω
two-x x y h y0 =
  trans (cong (λ t → mulZω twoZ t) (sym (x-from-y x y h)))
    (trans (sym (mulZω-assoc twoZ D₁ y))
      (trans (cong (λ t → mulZω (mulZω twoZ D₁) t) y0)
             (mulZω-zeroʳ (mulZω twoZ D₁))))

--------------------------------------------------------------------------------
-- ⑧ 主定理：2 维旋量表示没有不变直线
--
--   不变线 = Σ[ v ] (v ≠ 0) × (∀ g, ∃ c, ρ(g)·v = c·v)
--   由 E1、E2 消元得 2·x = 2·y = 0，无挠 ⇒ x = y = 0 ⇒ v = 0，矛盾。
--------------------------------------------------------------------------------

no-invariant-line :
    ¬ (Σ Pair (λ v →
         (v ≢ zeroV) ×
         (∀ (g : SL23) → Σ Zω (λ c → mulMV (toME g) v ≡ scaleV c v))))
no-invariant-line ((x , y) , vnz , inv) = vnz (cong₂ _,_ x0 y0)
  where
    E1h : mulZω cw2 y ≡ addZω y (mulZω cm1 x)
    E1h = E1 x y (proj₁ (inv g0)) (proj₁ (inv g9))
                 (proj₂ (inv g0)) (proj₂ (inv g9))

    E2h : addZω (mulZω cmw x) (mulZω cm1 y) ≡ mulZω cm1 x
    E2h = E2 x y (proj₁ (inv g0)) (proj₁ (inv g9))
                 (proj₂ (inv g0)) (proj₂ (inv g9))

    y0 : y ≡ zeroZω
    y0 = two-zero y (two-y x y E2h E1h)

    x0 : x ≡ zeroZω
    x0 = two-zero x (two-x x y (shift-E1 x y E1h) y0)
