{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.RH.NormD1
-- ℤ[i] 范数线: x² + y² = 4·3ⁿ 的基案分类（A1 · D1）
--
-- 数学背景（oracle norm-d1 冻结, 2026-11-25; n ≤ 12 全域枚举一致 ✓）:
--   · **3 惰性于 ℤ[i]**: x² + y² ≡ 0 (mod 3) ⟹ 3∣x ∧ 3∣y（平方 mod 3 ∈ {0,1},
--     1+1 = 2 ≢ 0）⟹ 解集 = 3·解集(n−2) 双坐标剥层递降;
--   · **可解 ⟺ n 偶**: n = 2k 时 (x,y) = (±2·3^k, 0) / (0, ±2·3^k);
--     **n 奇无解** —— 与 d=3 线的 t=0 谱系（NoNormT0Even）互为镜像。
--   · 负部由 ℤ 符号对称给出（未形式化, 同 Witness/NormClassify 边界）。
--
-- 本件（0 postulate, 独立具名引理形态）:
--   §1 载体 solD1 / BSolD1（偶-only Σ; oracle norm-d1 冻结陈述）
--   §2 系数-1 版上界链 xCap-le/yCap-le（承 NormClassify 的 ≤from≡/≤≡r/mono-sq）
--   §3 9≤4 空型（新封闭空型; 16≤12 复用 NormClassify）
--   §4 base0-thm: 9 格（2 冻结解见证 + 7 absurd）+ catch-all ×2
--   §5 base1-thm: **无解定理**（16 格 absurd + catch-all ×2; 奇指数镜面）
--   递降核（双坐标剥层）待续 —— 骨架同 NormClassify §7（tri3-split 双次）。

module Sovereign.Application.Problems.RH.NormD1 where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; s≤s)
open import Data.Nat.Properties
  using (≤-trans; m≤m+n; m≤n+m)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_)
open import Sovereign.Application.Problems.RH.NoNormT0Even
  using (module NoNormPrelude)
open import Sovereign.Application.Problems.RH.NormClassify
  using (mono-sq; ≤from≡; ≤≡r; ≤1↓; s≤0-empty; ↓4; 16≤12-empty)
open import Sovereign.Application.Problems.RH.Mod3Core
  using (tri3-split; no-suc-mult3)
open NoNormPrelude using (pow3; dub)

--------------------------------------------------------------------------------
-- §1. 载体（系数 1: x² + y², 区别于 d=3 的 x² + 3s²）
--------------------------------------------------------------------------------

solD1 : ℕ → ℕ → ℕ → Set
solD1 n x y = x * x + y * y ≡ 4 * pow3 n

-- v2 冻结（oracle norm-d1; 偶-only; 负部 ℤ 对称未形式化同前边界）
BSolD1 : ℕ → ℕ → ℕ → Set
BSolD1 n x y =
  Σ ℕ (λ k → n ≡ dub k × ((x ≡ 2 * pow3 k × y ≡ zero)
                        ⊎ (x ≡ zero × y ≡ 2 * pow3 k)))

--------------------------------------------------------------------------------
-- §2. 系数-1 版上界链（承 NormClassify 的 ≤from≡/≤≡r/mono-sq）
--------------------------------------------------------------------------------

xCap-le : ∀ N n x y → N ≤ x → solD1 n x y → N * N ≤ 4 * pow3 n
xCap-le N n x y le h =
  ≤-trans (mono-sq N x le)
          (≤from≡ (x * x) (y * y) (4 * pow3 n) h)

yCap-le : ∀ T n x y → T ≤ y → solD1 n x y → T * T ≤ 4 * pow3 n
yCap-le T n x y le h =
  ≤-trans (mono-sq T y le)
          (≤-trans (m≤n+m (y * y) (x * x))
                   (≤≡r (x * x + y * y) (4 * pow3 n) h))

--------------------------------------------------------------------------------
-- §3. 9≤4 空型（新封闭空型; 16≤12 复用 NormClassify）
--------------------------------------------------------------------------------

9≤4-empty : 3 * 3 ≤ 4 → ⊥
9≤4-empty h = s≤0-empty (↓4 h)

--------------------------------------------------------------------------------
-- §4. base0-thm（n = 0: x² + y² = 4; 冻结解 (0,2)/(2,0)）
--------------------------------------------------------------------------------

base0-thm : ∀ x y → solD1 0 x y → BSolD1 0 x y
base0-thm zero zero ()
base0-thm zero (suc zero) ()
base0-thm zero (suc (suc zero)) h = zero , refl , inj₂ (refl , refl)
base0-thm (suc zero) zero ()
base0-thm (suc zero) (suc zero) ()
base0-thm (suc zero) (suc (suc zero)) ()
base0-thm (suc (suc zero)) zero h = zero , refl , inj₁ (refl , refl)
base0-thm (suc (suc zero)) (suc zero) ()
base0-thm (suc (suc zero)) (suc (suc zero)) ()
-- x ≥ 3（任意 y）: 9 ≤ x² ≤ x² + y² ≡ 4
base0-thm (suc (suc (suc k))) y h =
  ⊥-elim (9≤4-empty (xCap-le 3 0 (suc (suc (suc k))) y (m≤m+n 3 k) h))
-- x = 0..2, y ≥ 3: 9 ≤ y² ≤ x² + y² ≡ 4
base0-thm zero (suc (suc (suc k))) h =
  ⊥-elim (9≤4-empty (yCap-le 3 0 zero (suc (suc (suc k))) (m≤m+n 3 k) h))
base0-thm (suc zero) (suc (suc (suc k))) h =
  ⊥-elim (9≤4-empty (yCap-le 3 0 (suc zero) (suc (suc (suc k))) (m≤m+n 3 k) h))
base0-thm (suc (suc zero)) (suc (suc (suc k))) h =
  ⊥-elim (9≤4-empty (yCap-le 3 0 (suc (suc zero)) (suc (suc (suc k))) (m≤m+n 3 k) h))

--------------------------------------------------------------------------------
-- §5. base1-thm（n = 1: x² + y² = 12 **无解** —— 奇指数镜面）
--     16 格全 absurd + x≥4 / y≥4 catch-all（16≤12 复用）
--------------------------------------------------------------------------------

base1-thm : ∀ x y → solD1 (suc zero) x y → ⊥
base1-thm zero zero ()
base1-thm zero (suc zero) ()
base1-thm zero (suc (suc zero)) ()
base1-thm zero (suc (suc (suc zero))) ()
base1-thm (suc zero) zero ()
base1-thm (suc zero) (suc zero) ()
base1-thm (suc zero) (suc (suc zero)) ()
base1-thm (suc zero) (suc (suc (suc zero))) ()
base1-thm (suc (suc zero)) zero ()
base1-thm (suc (suc zero)) (suc zero) ()
base1-thm (suc (suc zero)) (suc (suc zero)) ()
base1-thm (suc (suc zero)) (suc (suc (suc zero))) ()
base1-thm (suc (suc (suc zero))) zero ()
base1-thm (suc (suc (suc zero))) (suc zero) ()
base1-thm (suc (suc (suc zero))) (suc (suc zero)) ()
base1-thm (suc (suc (suc zero))) (suc (suc (suc zero))) ()
-- x ≥ 4（任意 y）: 16 ≤ x² ≤ x² + y² ≡ 12
base1-thm (suc (suc (suc (suc k)))) y h =
  ⊥-elim (16≤12-empty (xCap-le 4 1 (suc (suc (suc (suc k)))) y (m≤m+n 4 k) h))
-- x = 0..3, y ≥ 4: 16 ≤ y² ≤ x² + y² ≡ 12
base1-thm zero (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 zero (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base1-thm (suc zero) (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 (suc zero) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base1-thm (suc (suc zero)) (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 (suc (suc zero)) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
base1-thm (suc (suc (suc zero))) (suc (suc (suc (suc k)))) h =
  ⊥-elim (16≤12-empty (yCap-le 4 1 (suc (suc (suc zero))) (suc (suc (suc (suc k)))) (m≤m+n 4 k) h))
