{-# OPTIONS --rewriting --guardedness #-}

-- | _ProbeHCU1（探针：线1——unique-root₃-same 的 q≥2 分支，逐字镜像主模块子句）
-- 数学背景：x = 1 + q·(3¹¹·2¹⁵)，q ≥ 2 → x ≥ 1 + 2·M = 1 + 2M > 2M = N = SOVEREIGN_LCM
--   与 x < N 矛盾。N ≡ M + M 由 M ≡ 3¹¹·2¹⁵（M≡）+ 全字面量归约（refl 级）闭合。
-- 用途：主模块其余 11 个洞属线2/线3（本批排除），此探针为线1分支提供独立内核回执。
module _ProbeHCU1 where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-step; ≤-reflexive; ≤-<-trans; n≮n; +-assoc; +-identityʳ; +-suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Sovereign.Algebra.Hensel3Side using (pow3)
open import Sovereign.Algebra.Hensel2Side using (pow2)
open import Sovereign.Algebra.SovereignLCMRoots using (SOVEREIGN_LCM)

-- 主模块 m≤m+n-f 的逐字复制（a ≤ a + b，b 归纳）
m≤m+n-f : ∀ a b → a ≤ a + b
m≤m+n-f a zero = ≤-reflexive (sym (+-identityʳ a))
m≤m+n-f a (suc b) = subst (a ≤_) (sym (+-suc a b)) (≤-step (m≤m+n-f a b))

-- 线1 q≥2 分支（= 主模块 q-split-gen M (suc (suc q)) 子句的独立陈述）
qge2-branch : ∀ M q x' → M ≡ pow3 11 * pow2 15
            → suc x' ≡ 1 + suc (suc q) * M
            → suc x' < SOVEREIGN_LCM → ⊥
qge2-branch M q x' M≡ eq2 x<N = ⊥-elim (n≮n SOVEREIGN_LCM (≤-<-trans N≤x x<N))
  where
    -- N≡MM（未来态锁定）：M ≡ 3¹¹·2¹⁵ → M + M ≡ 3¹¹·2¹⁵ + 3¹¹·2¹⁵ → 字面归约 = SOVEREIGN_LCM
    N≡MM : SOVEREIGN_LCM ≡ M + M
    N≡MM = sym (trans M+M≡A+A A+A≡N)
      where
        A : ℕ
        A = pow3 11 * pow2 15
        M+M≡A+A : M + M ≡ A + A
        M+M≡A+A = subst (λ w → M + M ≡ w + w) M≡ refl
        A+A≡N : A + A ≡ SOVEREIGN_LCM
        A+A≡N = refl
    -- chain：M + M ≤ M + M + q·M（m≤m+n-f）≤ 1 + (M + (M + q·M))
    chain : M + M ≤ 1 + (M + (M + q * M))
    chain = ≤-step (subst ((M + M) ≤_) (+-assoc M M (q * M)) (m≤m+n-f (M + M) (q * M)))
    N≤x : SOVEREIGN_LCM ≤ suc x'
    N≤x = ≤-trans (≤-reflexive N≡MM) (subst ((M + M) ≤_) (sym eq2) chain)
