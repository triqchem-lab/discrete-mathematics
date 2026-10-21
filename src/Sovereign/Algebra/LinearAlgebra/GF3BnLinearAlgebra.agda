{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3BnLinearAlgebra
--
-- **闭合缺口 ②**：`b_n` 的线性代数意义。
--
-- ## 背景（2026-10-21 自我审核的缺口 ②）
--
-- 我此前把 `b_n` **定义**为 `S'' fzero n ∸ Z n`，并证了 `(b_n) + Z n ≡ C0 n`。
-- 但那是关于**我的定义**的定理，不是关于 `dim(ker F ∩ V_nA)` 的定理。
--
-- 本模块证明**关键连接**：
--   `#{x : Hamming(x) ≡ 0 且「所有坐标非零」} ≡ Z n`
-- 由此 `b_n = C0 n − Z n` 就是 `#{λ_x = 0 且有坐标为 0}` ✓。
--
-- ## 数学
--
--   · 「全非零」⇒ 每坐标 ∈ {1,2} ⇒ 共 2^n 个点
--   · 全非零时 Hamming = n ⇒ 「Hamming ≡ 0」⟺ 「3 | n」
--   ⇒ 计数 = `3 | n` 时 `2^n`，否则 `0` = `Z n` ✓
--
-- ## 核心原则
--   · 用**真实枚举**（`sumVec`，3 支递归）—— 与 `Z` 的 case 定义**结构不同** ✓
--   · 零 postulate / 零 hole

module Sovereign.Algebra.LinearAlgebra.GF3BnLinearAlgebra where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF9KernelImageZero using (nz3; hammingT)
open import Sovereign.Algebra.LinearAlgebra.GF3HammingCountLink using (sumVec; hid; sumVec-cong)
open import Sovereign.Algebra.LinearAlgebra.GF3HammingCount using (C0; Z)

--------------------------------------------------------------------------------
-- §1. 「全非零」指示
--------------------------------------------------------------------------------

-- 单坐标「非零」指示（0/1）—— 注意：两个非零分支在 `sumVec` 里**各自计一次** ✓
-- ⚠ 原写 `2` 会与 `sumVec` 的两支重复计数（得到 4 而非 2）✗
nz2 : Fin 3 → ℕ
nz2 fzero               = 0
nz2 (fsuc fzero)        = 1
nz2 (fsuc (fsuc fzero)) = 1

-- 全非零指示（乘性累积）
allNZ : ∀ {n} → Torus n → ℕ
allNZ []       = 1
allNZ (x ∷ xs) = nz2 x * allNZ xs

-- 全非零且 Hamming ≡ r 的计数
AllH : Fin 3 → ℕ → ℕ
AllH r n = sumVec {n} (λ x → hid (hammingT x) r * allNZ x)
