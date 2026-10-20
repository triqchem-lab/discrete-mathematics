{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3BlockSplit
-- 系数表示的**块分解**（T4 的 b_n 闭式证明的第一块，2026-10-20）
--
-- 数学背景
--   `CoeffN n = Torus n → Trit` 是系数函数。把 `Torus (suc n)` 的首位当作
--   **新坐标** `x_0`，则任一系数函数 `p` 被它的三个**切片**唯一决定：
--     `splitAt p k = λ rest → p (k ∷ rest)`      （k = T₀ / T₁ / T₂）
--   `join` 是逆操作。`join-split` 说「先切再拼复原」（**点态**陈述，本库无 funext）。
--
-- 为什么需要
--   `F_n = Σ_j x_j²` 按「新坐标的幂次」分块后呈
--     `[[A,0,0],[0,A,0],[I,0,A]]`（A = F_{n−1}）
--   —— 这正是 `a_n = 2a_{n−1} + q_{n−1}` 与 `b_n = 3^{n−1} − 2^{n−1}` 的来源。
--
-- 0 postulate / 0 hole

module Sovereign.Algebra.LinearAlgebra.GF3BlockSplit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)

--------------------------------------------------------------------------------
-- §1. 三个切片与拼接
--------------------------------------------------------------------------------

CoeffN : ℕ → Set
CoeffN n = Torus n → Trit

-- 第 k 个切片：把首位固定为 k
splitAt : ∀ {n} → CoeffN (suc n) → Fin 3 → CoeffN n
splitAt p k rest = p (k ∷ rest)

-- 拼接：按首位分三支
join : ∀ {n} → CoeffN n → CoeffN n → CoeffN n → CoeffN (suc n)
join q0 q1 q2 (fzero ∷ rest)             = q0 rest
join q0 q1 q2 (fsuc fzero ∷ rest)        = q1 rest
join q0 q1 q2 (fsuc (fsuc fzero) ∷ rest) = q2 rest

--------------------------------------------------------------------------------
-- §2. 先切再拼复原（**点态**，因为本库不假设 funext）
--------------------------------------------------------------------------------

join-split : ∀ {n} (p : CoeffN (suc n)) (x : Torus (suc n)) →
  join (splitAt p fzero) (splitAt p (fsuc fzero)) (splitAt p (fsuc (fsuc fzero))) x ≡ p x
join-split p (fzero ∷ rest)             = refl
join-split p (fsuc fzero ∷ rest)        = refl
join-split p (fsuc (fsuc fzero) ∷ rest) = refl

-- 反向：先拼再切（三条）
split-join-0 : ∀ {n} (q0 q1 q2 : CoeffN n) (rest : Torus n) →
  splitAt (join q0 q1 q2) fzero rest ≡ q0 rest
split-join-0 q0 q1 q2 rest = refl

split-join-1 : ∀ {n} (q0 q1 q2 : CoeffN n) (rest : Torus n) →
  splitAt (join q0 q1 q2) (fsuc fzero) rest ≡ q1 rest
split-join-1 q0 q1 q2 rest = refl

split-join-2 : ∀ {n} (q0 q1 q2 : CoeffN n) (rest : Torus n) →
  splitAt (join q0 q1 q2) (fsuc (fsuc fzero)) rest ≡ q2 rest
split-join-2 q0 q1 q2 rest = refl

--------------------------------------------------------------------------------
-- §3. 老坐标上的乘子与切片交换（关键：两边都归约到同一个 with，故 refl 可证）
--------------------------------------------------------------------------------

open import Sovereign.Base.Trit using (_⊕_; ⊕-identityˡ)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (sumFin; sumFin-cong)
open import Sovereign.Algebra.LinearAlgebra.GF3Barrier using (mulX2; lookupAt)

-- 老坐标 j = fsuc i 上的 `mulX2` 与切片交换
mulX2-slice : ∀ {n} (i : Fin n) (p : CoeffN (suc n)) (k : Fin 3) (rest : Torus n) →
  mulX2 (fsuc i) p (k ∷ rest) ≡ mulX2 i (splitAt p k) rest
mulX2-slice i p k rest with lookupAt i rest
... | fzero             = refl
... | fsuc fzero        = refl
... | fsuc (fsuc fzero) = refl

--------------------------------------------------------------------------------
-- §4. `sum2` 的块恒等式（= 块矩阵 [[A,0,0],[0,A,0],[I,0,A]]）
--------------------------------------------------------------------------------

sum2 : ∀ {n} → CoeffN n → CoeffN n
sum2 p x = sumFin (λ j → mulX2 j p x)

-- 把 sumFin 按首位（新坐标）拆开
sumFin-split : ∀ {n} (g : Fin (suc n) → Trit) →
  sumFin g ≡ g fzero ⊕ sumFin (λ i → g (fsuc i))
sumFin-split g = refl

-- ★ 块恒等式：`F_{n+1}` 在新坐标 k 处的值 = 新坐标项 ⊕ 老坐标的 `F_n`（作用在切片上）
--
--   k = T₀：`F` 的新坐标项为 0（x₀² 把指数推到 2，越界）⇒ 只有 A p₀
--   k = T₁：同上 ⇒ 只有 A p₁
--   k = T₂：新坐标项 = p₀（回退一位）⇒ p₀ ⊕ A p₂
-- 新坐标上的项：k = T₀/T₁ 时归零；k = T₂ 时等于 p₀
mulX2-new-0 : ∀ {n} (p : CoeffN (suc n)) (rest : Torus n) →
  mulX2 fzero p (fzero ∷ rest) ≡ T₀
mulX2-new-0 p rest = refl

mulX2-new-1 : ∀ {n} (p : CoeffN (suc n)) (rest : Torus n) →
  mulX2 fzero p (fsuc fzero ∷ rest) ≡ T₀
mulX2-new-1 p rest = refl

mulX2-new-2 : ∀ {n} (p : CoeffN (suc n)) (rest : Torus n) →
  mulX2 fzero p (fsuc (fsuc fzero) ∷ rest) ≡ splitAt p fzero rest
mulX2-new-2 p rest = refl

sum2-block-0 : ∀ {n} (p : CoeffN (suc n)) (rest : Torus n) →
  sum2 p (fzero ∷ rest) ≡ sum2 (splitAt p fzero) rest
sum2-block-0 p rest =
  trans (cong (λ z → z ⊕ sumFin (λ i → mulX2 (fsuc i) p (fzero ∷ rest)))
              (mulX2-new-0 p rest))
        (trans (cong (λ z → T₀ ⊕ z)
                     (sumFin-cong (λ i → mulX2-slice i p fzero rest)))
               (⊕-identityˡ (sumFin (λ i → mulX2 i (splitAt p fzero) rest))))

sum2-block-1 : ∀ {n} (p : CoeffN (suc n)) (rest : Torus n) →
  sum2 p (fsuc fzero ∷ rest) ≡ sum2 (splitAt p (fsuc fzero)) rest
sum2-block-1 p rest =
  trans (cong (λ z → z ⊕ sumFin (λ i → mulX2 (fsuc i) p (fsuc fzero ∷ rest)))
              (mulX2-new-1 p rest))
        (trans (cong (λ z → T₀ ⊕ z)
                     (sumFin-cong (λ i → mulX2-slice i p (fsuc fzero) rest)))
               (⊕-identityˡ (sumFin (λ i → mulX2 i (splitAt p (fsuc fzero)) rest))))

sum2-block-2 : ∀ {n} (p : CoeffN (suc n)) (rest : Torus n) →
  sum2 p (fsuc (fsuc fzero) ∷ rest)
    ≡ splitAt p fzero rest ⊕ sum2 (splitAt p (fsuc (fsuc fzero))) rest
sum2-block-2 p rest =
  trans (cong (λ z → z ⊕ sumFin (λ i → mulX2 (fsuc i) p (fsuc (fsuc fzero) ∷ rest)))
              (mulX2-new-2 p rest))
        (cong (λ z → splitAt p fzero rest ⊕ z)
              (sumFin-cong (λ i → mulX2-slice i p (fsuc (fsuc fzero)) rest)))
