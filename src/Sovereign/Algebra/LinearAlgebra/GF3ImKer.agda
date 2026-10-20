{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3ImKer
-- ★ `im F ∩ ker F = F(ker F²)`（T4 的 q_n 结构恒等式，2026-10-20）
--
-- 数学背景
--   `F = F_n = Σ_j x_j²`（GF(3) 上的拉普拉斯）。记
--     `im F  = {F q}`、`ker F = {p : F p = 0}`、`ker F² = {q : F² q = 0}`。
--
--   **定理（本模块）**：`im F ∩ ker F = F(ker F²)` —— **子空间相等**。
--
--   证明是三条平凡包含：
--     ① `F(ker F²) ⊆ im F`      —— 就是 `F` 的像
--     ② `F(ker F²) ⊆ ker F`     —— `F(F q) = F² q = 0`
--     ③ `im F ∩ ker F ⊆ F(ker F²)` —— `p = F q` 且 `F p = 0` ⇒ `F² q = 0`
--
--   这条等式是 oracle 恒等式 `q_n = c_n − a_n` 的**结构内容**
--   （取维数即得 `q_n = dim ker F² − dim ker F = c_n − a_n`）。
--   **本模块只证结构等式** ✓ —— 维数推论需要秩-零化度，本库暂无 ✗。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3ImKer where

open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF3BlockSplit using (CoeffN; sum2)

--------------------------------------------------------------------------------
-- §0. 点态同余：函数在每点相等 ⇒ `sum2` 后的值相等
--
-- 本库无 funext ⇒ 不能用 `cong` 改写函数；必须走这条逐点同余。
--------------------------------------------------------------------------------

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (mulX2; lookupAt; zeroAt)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin-cong)

-- `mulX2` 只看 `p` 在一个点上的值 ⇒ 逐点相等就够了
mulX2-cong : ∀ {n} (i : Fin n) (p p' : CoeffN n) →
  (∀ y → p y ≡ p' y) → (b : Torus n) → mulX2 i p b ≡ mulX2 i p' b
mulX2-cong i p p' eq b with lookupAt i b
... | fzero             = refl
... | fsuc fzero        = refl
... | fsuc (fsuc fzero) = eq (zeroAt i b)

-- ★ `sum2` 的逐点同余
sum2-cong : ∀ {n} (p p' : CoeffN n) →
  (∀ y → p y ≡ p' y) → ∀ x → sum2 p x ≡ sum2 p' x
sum2-cong {n} p p' eq x = sumFin-cong {n = n} (λ j → mulX2-cong j p p' eq x)

--------------------------------------------------------------------------------
-- §1. 三个集合（都是 `CoeffN n` 上的谓词，点态形式）
--------------------------------------------------------------------------------

-- 像：`p` 是某个 `q` 的像
ImF : ∀ {n} → CoeffN n → Set
ImF {n} p = Σ (CoeffN n) (λ q → ∀ x → p x ≡ sum2 q x)

-- 核：`p` 被 `F` 杀掉
KerF : ∀ {n} → CoeffN n → Set
KerF p = ∀ x → sum2 p x ≡ T₀

-- `F(ker F²)`：`p` 是某个**二阶核元素**的像
ImgKerF2 : ∀ {n} → CoeffN n → Set
ImgKerF2 {n} p =
  Σ (CoeffN n) (λ q → (∀ x → sum2 (sum2 q) x ≡ T₀) × (∀ x → p x ≡ sum2 q x))

--------------------------------------------------------------------------------
-- §2. 三条包含
--------------------------------------------------------------------------------

-- ① `F(ker F²) ⊆ im F`
imgker⊆im : ∀ {n} {p : CoeffN n} → ImgKerF2 p → ImF p
imgker⊆im (q , _ , pq) = q , pq

-- ② `F(ker F²) ⊆ ker F`：`F(F q) = F² q = 0`
imgker⊆ker : ∀ {n} {p : CoeffN n} → ImgKerF2 p → KerF p
imgker⊆ker {n} {p} (q , F2q , pq) x =
  trans (sum2-cong p (sum2 q) pq x) (F2q x)

-- ③ `im F ∩ ker F ⊆ F(ker F²)`：`p = F q` 且 `F p = 0` ⇒ `F² q = 0`
im∩ker⊆imgker : ∀ {n} {p : CoeffN n} → ImF p → KerF p → ImgKerF2 p
im∩ker⊆imgker {n} {p} (q , pq) kerp = q , F2q , pq
  where
    -- `F² q = F p = 0`
    F2q : ∀ x → sum2 (sum2 q) x ≡ T₀
    F2q x = trans (sym (sum2-cong p (sum2 q) pq x)) (kerp x)

--------------------------------------------------------------------------------
-- §3. ★ 主定理：`im F ∩ ker F = F(ker F²)`
--------------------------------------------------------------------------------

-- 正向：交 ⊆ `F(ker F²)`
imkapker→imgker : ∀ {n} {p : CoeffN n} → ImF p × KerF p → ImgKerF2 p
imkapker→imgker (im , ker) = im∩ker⊆imgker im ker

-- 反向：`F(ker F²)` ⊆ 交
imgker→imkapker : ∀ {n} {p : CoeffN n} → ImgKerF2 p → ImF p × KerF p
imgker→imkapker ik = imgker⊆im ik , imgker⊆ker ik

-- ★ 子空间相等（双向）
im-ker-eq : ∀ {n} (p : CoeffN n) →
  (ImgKerF2 p → ImF p × KerF p) × (ImF p × KerF p → ImgKerF2 p)
im-ker-eq p = imgker→imkapker , imkapker→imgker

--------------------------------------------------------------------------------
-- §4. 与幂等/平方的关系（供后续维数推论使用）
--------------------------------------------------------------------------------

-- `F` 在 `ker F²` 上的像恰是 `im F ∩ ker F`（重述，便于查用）
im-of-kerF2 : ∀ {n} {p : CoeffN n} →
  (Σ (CoeffN n) (λ q → (∀ x → sum2 (sum2 q) x ≡ T₀) × (∀ x → p x ≡ sum2 q x)))
  → ImF p × KerF p
im-of-kerF2 = imgker→imkapker
