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

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_)
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

--------------------------------------------------------------------------------
-- §2. ❌ `AllH` 的递推：**未完成**（诚实标注，2026-10-21）
--
-- 数学上确定 ✓（数值验证 n=0..7 ✓）：
--   `AllH r (suc n) = 2 * AllH (pred3 r) n`
--   （v=0 支 ∵ nz2 fzero = 0 ⇒ 0；v=1,2 支各得 `AllH (pred3 r) n`）
--
-- ❌ 组装障碍：
--   `Z n = Zr (mod3 n) n` 是**按 mod3 索引**的 ✗，不是递推 ✗
--   ⇒ `AllH` 的递推（步长 2）与 `Z` 的 mod3 周期（步长 3）**不同构** ✗
--   ⇒ 需要**在归纳中追踪 `mod3`**（3-周期 + 算术）✗ —— ~60 行未做 ✗
--
-- 下一步（明确）：
--   ★AllH-aux : ∀ n (r : Fin 3) → mod3 n ≡ r → AllH fzero n ≡ Zr r n
--   （用显式等式参数，避开 `with` 不抽象 β-归约项的问题 —— §31.3 模板）
--------------------------------------------------------------------------------

-- 已确切验证的数值事实（Python 真实枚举 n=0..7）：
--   AllH 0 n = 1, 0, 0, 8, 0, 0, 64, 0
--   Z n      = 1, 0, 0, 8, 0, 0, 64, 0        ✓ 完全一致

--------------------------------------------------------------------------------
-- §3. `AllH` 的递推（用 §44 查到的 `suc(suc(suc n))` 3-周期模板）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.GF3HammingCountLink using (hid-one)
open import Sovereign.Algebra.LinearAlgebra.GF3HammingCount using (pred3)
open import Data.Nat.Properties using (+-identityʳ; +-assoc; *-identityʳ; *-zeroʳ)
open import Data.Nat.Properties using (+-*-commutativeSemiring)
open import Algebra.Solver.Ring.NaturalCoefficients.Default +-*-commutativeSemiring

-- ① `sumVec (λ _ → 0)` = 0
sumVec-zero : ∀ {n} → sumVec {n} (λ _ → 0) ≡ 0
sumVec-zero {zero}  = refl
sumVec-zero {suc n} =
  trans (cong₂ _+_ (cong₂ _+_ (sumVec-zero {n}) (sumVec-zero {n})) (sumVec-zero {n})) refl

-- `1 * z ≡ z`
one-* : ∀ z → 1 * z ≡ z
one-* z = +-identityʳ z

-- `0 + (a + a) ≡ 2 * a`
two-of : ∀ a → 0 + (a + a) ≡ 2 * a
two-of = solve 1 (λ a → con 0 :+ (a :+ a) := con 2 :* a) refl

-- ② `AllH r (suc n) ≡ 2 * AllH (pred3 r) n`
AllH-rec : ∀ (r : Fin 3) (n : ℕ) → AllH r (suc n) ≡ 2 * AllH (pred3 r) n
AllH-rec r n =
  trans (cong₂ _+_
          (cong₂ _+_
            (trans (sumVec-cong {n} (λ xs → z-branch r xs)) (sumVec-zero {n}))
            (sumVec-cong {n} (λ xs → o-branch r xs)))
          (sumVec-cong {n} (λ xs → o-branch r xs)))
        (two-of (AllH (pred3 r) n))
  where
    z-branch : ∀ (r : Fin 3) (xs : Torus n) →
      hid (nz3 fzero ⊕ hammingT xs) r * (nz2 fzero * allNZ xs) ≡ 0
    z-branch r xs = *-zeroʳ (hid (nz3 fzero ⊕ hammingT xs) r)

    o-branch : ∀ (r : Fin 3) (xs : Torus n) →
      hid (nz3 (fsuc fzero) ⊕ hammingT xs) r * (nz2 (fsuc fzero) * allNZ xs)
      ≡ hid (hammingT xs) (pred3 r) * allNZ xs
    o-branch r xs =
      trans (cong (λ w → w * (1 * allNZ xs)) (hid-one (hammingT xs) r))
            (trans (cong (λ w → hid (hammingT xs) (pred3 r) * w) (one-* (allNZ xs))) refl)

--------------------------------------------------------------------------------
-- §4. ★★★★ 主定理：`AllH fzero n ≡ Z n`（3-周期归纳）
--------------------------------------------------------------------------------

open import Sovereign.Algebra.LinearAlgebra.GF3HammingCount using (mod3; Zr)

-- `mod3` 的 3-周期（定义）
mod3-suc3 : ∀ n → mod3 (suc (suc (suc n))) ≡ mod3 n
mod3-suc3 n = refl

-- `Zr r` 的 3-步缩放
Zr-scale : ∀ (r : Fin 3) n → Zr r (suc (suc (suc n))) ≡ 8 * Zr r n
Zr-scale fzero n = solve 1 (λ a → con 2 :* (con 2 :* (con 2 :* a)) := con 8 :* a) refl (2 ^ n)
Zr-scale (fsuc fzero) n = sym (*-zeroʳ 8)
Zr-scale (fsuc (fsuc fzero)) n = sym (*-zeroʳ 8)

-- `Z` 的 3-步缩放
Z-scale : ∀ n → Z (suc (suc (suc n))) ≡ 8 * Z n
Z-scale n = Zr-scale (mod3 (suc (suc (suc n)))) n

-- `AllH fzero` 的 3-步缩放（三次 `AllH-rec`）
AllH-scale : ∀ n → AllH fzero (suc (suc (suc n))) ≡ 8 * AllH fzero n
AllH-scale n =
  trans (AllH-rec fzero (suc (suc n)))
        (trans (cong (2 *_) (AllH-rec (pred3 fzero) (suc n)))
               (trans (cong (2 *_) (cong (2 *_) (AllH-rec (pred3 (pred3 fzero)) n)))
                      (solve 1 (λ a → con 2 :* (con 2 :* (con 2 :* a)) := con 8 :* a) refl (AllH fzero n))))

-- ★★★★ `AllH fzero n ≡ Z n`
★AllH : ∀ n → AllH fzero n ≡ Z n
★AllH zero                  = refl
★AllH (suc zero)            = refl
★AllH (suc (suc zero))      = refl
★AllH (suc (suc (suc n)))   =
  trans (AllH-scale n)
        (trans (cong (8 *_) (★AllH n)) (sym (Z-scale n)))
