{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3HammingCountLink
--
-- **闭合「影子」缺口**：`C0`（递归序列）确实等于 Hamming 计数。
--
-- ## 背景（2026-10-21 自我审核发现的缺口 ①）
--
-- `GF3HammingCount.agda` 里 `C0/C1/C2` 是**纯递归定义**：
--   `C0 0 = 1`，`C0 (suc n) = C0 n + 2 * C2 n`（余者类推）
-- 而「`C_r n` = #{x : Hamming(x) ≡ r mod 3}」只写在**注释**里 ✗ —— 未证。
--
-- 本模块用**真实枚举**（`sumVec`，遍历 (Fin 3)^n 的全部 3^n 个点）
-- 定义计数 `Cnt r n`，并证明 `Cnt r n ≡ C_r n`。
--
-- ## 为什么不是同义反复
--
--   · `sumVec` 的递归：**枚举** —— `3` 支 × 递归（`Σ_{v∈Fin 3}`）
--   · `C0` 的递归：**线性组合** —— `C0 n + 2 * C2 n`
--   ⇒ 两者递归结构**不同** ⇒ 定理有真实内容 ✓
--
-- ## 核心原则
--   · 零 postulate / 零 hole
--   · 枚举穷尽（`Fin 3` 的 3 个构造子全部覆盖）

module Sovereign.Algebra.LinearAlgebra.GF3HammingCountLink where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_)
open import Sovereign.Algebra.LinearAlgebra.GF3LaplacianN using (Torus)
open import Sovereign.Algebra.LinearAlgebra.GF9KernelImageZero using (nz3; hammingT)
open import Sovereign.Algebra.LinearAlgebra.GF3HammingCount using (C0; C1; C2)

--------------------------------------------------------------------------------
-- §1. 真实枚举：对 (Fin 3)^n 的全部点求和
--------------------------------------------------------------------------------

-- 真实枚举：3 支覆盖 `Fin 3` 的全部构造子，递归在**尾部**上
sumVec : ∀ {n} → (Torus n → ℕ) → ℕ
sumVec {zero}  f = f []
sumVec {suc n} f =
    sumVec {n} (λ xs → f (fzero ∷ xs))
  + sumVec {n} (λ xs → f (fsuc fzero ∷ xs))
  + sumVec {n} (λ xs → f (fsuc (fsuc fzero) ∷ xs))

--------------------------------------------------------------------------------
-- §2. 指示函数与计数
--------------------------------------------------------------------------------

-- `hid h r` = 1 若 `h` 对应 `r`，否则 0
hid : Trit → Fin 3 → ℕ
hid T₀ fzero                 = 1
hid T₀ (fsuc _)              = 0
hid T₁ fzero                 = 0
hid T₁ (fsuc fzero)          = 1
hid T₁ (fsuc (fsuc _))       = 0
hid T₂ fzero                 = 0
hid T₂ (fsuc fzero)          = 0
hid T₂ (fsuc (fsuc fzero))   = 1

-- 真实计数：`Cnt r n = #{x : Torus n : hammingT x ↔ r}`
Cnt : Fin 3 → ℕ → ℕ
Cnt r n = sumVec {n} (λ x → hid (hammingT x) r)

-- `C_r` 的三支封装
Cr : Fin 3 → ℕ → ℕ
Cr fzero              = C0
Cr (fsuc fzero)       = C1
Cr (fsuc (fsuc _))    = C2

--------------------------------------------------------------------------------
-- §3. ★★★ 主定理：`Cnt r n ≡ C_r n`（真实计数 = 递归序列）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.GF3HammingCount using (pred3)

-- `T₀ ⊕ h ≡ h`（定义）
hid-zero : ∀ (h : Trit) (r : Fin 3) → hid (T₀ ⊕ h) r ≡ hid h r
hid-zero T₀ r = refl
hid-zero T₁ r = refl
hid-zero T₂ r = refl

-- `T₁ ⊕ h` 对应「余数前移一位」
hid-one : ∀ (h : Trit) (r : Fin 3) → hid (T₁ ⊕ h) r ≡ hid h (pred3 r)
hid-one T₀ fzero              = refl
hid-one T₀ (fsuc fzero)       = refl
hid-one T₀ (fsuc (fsuc fzero)) = refl
hid-one T₁ fzero              = refl
hid-one T₁ (fsuc fzero)       = refl
hid-one T₁ (fsuc (fsuc fzero)) = refl
hid-one T₂ fzero              = refl
hid-one T₂ (fsuc fzero)       = refl
hid-one T₂ (fsuc (fsuc fzero)) = refl

-- 枚举求和同余
sumVec-cong : ∀ {n} {f g : Torus n → ℕ} → (∀ x → f x ≡ g x) → sumVec f ≡ sumVec g
sumVec-cong {zero}  h = h []
sumVec-cong {suc n} h =
  cong₂ _+_ (cong₂ _+_
              (sumVec-cong {n} (λ xs → h (fzero ∷ xs)))
              (sumVec-cong {n} (λ xs → h (fsuc fzero ∷ xs))))
            (sumVec-cong {n} (λ xs → h (fsuc (fsuc fzero) ∷ xs)))

-- `a + b + b ≡ a + 2 * b`
open import Data.Nat.Properties using (+-assoc; +-identityʳ; *-suc)

open import Data.Nat.Properties using (+-*-commutativeSemiring)
open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-commutativeSemiring

assoc2 : ∀ a b → (a + b) + b ≡ a + 2 * b
assoc2 = solve 2 (λ a b → (a :+ b) :+ b := a :+ con 2 :* b) refl

--------------------------------------------------------------------------------
-- §4. ★★★★ 主定理：真实计数 = 递归序列
--------------------------------------------------------------------------------

-- 归纳步（IH 作参数，避免循环）
stepCnt : ∀ (r : Fin 3) (n : ℕ) →
  Cnt r n ≡ Cr r n → Cnt (pred3 r) n ≡ Cr (pred3 r) n →
  Cnt r (suc n) ≡ Cr r n + 2 * Cr (pred3 r) n
stepCnt r n ih ih' =
  trans step-red
        (trans (assoc2 (Cnt r n) (Cnt (pred3 r) n))
               (cong₂ _+_ ih (cong (2 *_) ih')))
  where
    step-red : Cnt r (suc n) ≡ (Cnt r n + Cnt (pred3 r) n) + Cnt (pred3 r) n
    step-red =
      cong₂ _+_
        (cong₂ _+_
          (sumVec-cong {n} (λ xs → hid-zero (hammingT xs) r))
          (sumVec-cong {n} (λ xs → hid-one (hammingT xs) r)))
        (sumVec-cong {n} (λ xs → hid-one (hammingT xs) r))

-- ★★★★ 主定理：真实计数 = 递归序列
★Cnt : ∀ (r : Fin 3) (n : ℕ) → Cnt r n ≡ Cr r n
★Cnt fzero            zero    = refl
★Cnt (fsuc fzero)     zero    = refl
★Cnt (fsuc (fsuc fzero)) zero = refl
★Cnt fzero            (suc n) = stepCnt fzero n (★Cnt fzero n) (★Cnt (pred3 fzero) n)
★Cnt (fsuc fzero)     (suc n) = stepCnt (fsuc fzero) n (★Cnt (fsuc fzero) n) (★Cnt (pred3 (fsuc fzero)) n)
★Cnt (fsuc (fsuc fzero)) (suc n) =
  stepCnt (fsuc (fsuc fzero)) n (★Cnt (fsuc (fsuc fzero)) n) (★Cnt (pred3 (fsuc (fsuc fzero))) n)

-- ★★★★ 结论：`C0` 就是 Hamming 计数（缺口 ① 闭合）
★C0-is-hamming : ∀ n → Cnt fzero n ≡ C0 n
★C0-is-hamming n = ★Cnt fzero n

★C1-is-hamming : ∀ n → Cnt (fsuc fzero) n ≡ C1 n
★C1-is-hamming n = ★Cnt (fsuc fzero) n

★C2-is-hamming : ∀ n → Cnt (fsuc (fsuc fzero)) n ≡ C2 n
★C2-is-hamming n = ★Cnt (fsuc (fsuc fzero)) n
