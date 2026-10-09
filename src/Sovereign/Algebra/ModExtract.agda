{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.ModExtract
-- mod 形提取引理（唯一性 mod 形改造的核心件）：x ≡ r + q·N → x < N → x ≡ r
--
-- 数学背景：唯一性等式层的 cancel 边界（literal 归纳）绕法——改 mod 形陈述：
--   x ≡ r + q·N 形的 q 提取（对 q 归纳——q 是符号 ✓ 零 literal 归纳）：
--   q = 0 → x ≡ r（identity 桥）；q ≥ 1 → x ≥ N（m≤m+n 链）与 x < N 矛盾。
--
-- 核心原则：
-- 1. 对 q 符号归纳（零 literal 归纳——经验 44 条的正形）
-- 2. 纯构造（refl/≤ 链/clash——零 mod-helper 零符号消去）
-- 3. 与 HenselCRTUniqueness 的唯一性层衔接（mod 形改造的核心引理）
--
-- 包含：mod-extract（q=0 提取）/ mod-extract-le（≤ 形变体）

module Sovereign.Algebra.ModExtract where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-trans; ≤-<-trans; n≮n; +-comm; +-assoc; +-identityʳ)

-- q 形提取：x ≡ r + q·N → x < N → x ≡ r（对 q 归纳——符号安全）
mod-extract : ∀ (N r : ℕ) → ∀ x q → x ≡ r + q * N → x < N → x ≡ r
mod-extract N r x zero eq x<N = trans eq (+-identityʳ r)
mod-extract N r x (suc q) eq x<N = ⊥-elim (n≮n N (≤-<-trans N≤x x<N))
  where
    -- N ≤ x：x = r + (suc q)·N = r + (N + q·N) → N ≤ N + q·N ≤ r + N + q·N = x
    N≤sucqN : N ≤ suc q * N
    N≤sucqN = subst (N ≤_) (sym (suc-q-form q)) (m≤m+n N (q * N))
      where
        suc-q-form : ∀ q → N + q * N ≡ suc q * N
        suc-q-form q = refl
    N≤x : N ≤ x
    N≤x = subst (N ≤_) (sym eq) (≤-trans N≤sucqN (m≤n+m (suc q * N) r))
