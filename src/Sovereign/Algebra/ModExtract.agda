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

open import Data.Nat using (ℕ; zero; suc; pred; _*_; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-trans; ≤-<-trans; n≮n; +-comm; +-assoc; +-identityʳ; +-suc)

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

-- ────────────────────────────────────────────────────────────────────
-- §2. plus-cancel：加法消去的符号归纳版（对 C 归纳——经验 44 条正形）
--   a + C ≡ (D + C) + q·N → a ≡ D + q·N（消 C 不消 q·N——免 literal 归纳）
-- ────────────────────────────────────────────────────────────────────

plus-cancel : ∀ (a D C q N : ℕ) → a + C ≡ (D + C) + q * N → a ≡ D + q * N
plus-cancel a D zero q N eq =
  trans (sym (+-identityʳ a))
  (trans eq (cong (_+ q * N) (+-identityʳ D)))
plus-cancel a D (suc C) q N eq =
  plus-cancel a D C q N (suc-injective-f (trans (sym (+-suc a C))
    (trans eq (cong (_+ q * N) (+-suc D C)))))
  where
    suc-injective-f : ∀ {x y} → suc x ≡ suc y → x ≡ y
    suc-injective-f refl = refl

-- DB case 应用形（唯一性 mod 形改造）：a + C ≡ suc q·2¹⁶（defeq 同 (D + C) + q·2¹⁶ 形）
db-mod-extract : ∀ a q → a + 2 * 24371 ≡ suc q * 65536 → a < 65536 → a ≡ 16794 + q * 65536
db-mod-extract a q eq a< = plus-cancel a 16794 (2 * 24371) q 65536 eq

-- ────────────────────────────────────────────────────────────────────
-- §3. ∣-diff：整除差引理（d∣m → d∣n → d∣m∸n——∸-distrib 形）
-- ────────────────────────────────────────────────────────────────────

open import Data.Nat using (_∸_)
open import Data.Nat.Divisibility using (_∣_; divides)
open import Data.Nat.Properties using (*-distribʳ-∸)

∣-diff : ∀ {d m n} → d ∣ m → d ∣ n → d ∣ (m ∸ n)
∣-diff {d} {m} {n} (divides k1 e1) (divides k2 e2) =
  divides (k1 ∸ k2) (trans (cong₂ _∸_ e1 e2) (sym (*-distribʳ-∸ d k1 k2)))

-- ────────────────────────────────────────────────────────────────────
-- §4. ∸+-cancel（自证——对 o 符号归纳）+ div2-side（2¹⁶ 侧闭合）
-- ────────────────────────────────────────────────────────────────────

open import Data.Nat.Properties using (n+1≡suc; pred[m∸n]≡m∸[1+n]; 0∸n≡0)

suc∸suc : ∀ a b → suc a ∸ suc b ≡ a ∸ b
suc∸suc a zero = refl
suc∸suc a (suc b) = trans (sym (pred[m∸n]≡m∸[1+n] (suc a) (suc b)))
  (trans (cong pred (suc∸suc a b)) (pred[m∸n]≡m∸[1+n] a b))

∸+-cancel : ∀ m n o → (m + o) ∸ (n + o) ≡ m ∸ n
∸+-cancel m n zero = cong₂ _∸_ (+-identityʳ m) (+-identityʳ n)
∸+-cancel m n (suc o) =
  trans (cong₂ _∸_ (+-suc m o) (+-suc n o))
  (trans (suc∸suc (m + o) (n + o)) (∸+-cancel m n o))


-- ────────────────────────────────────────────────────────────────────
-- §5. ∸∸-align（条件形——n = suc n' 时免归纳：case 分裂 + suc∸suc）
-- ────────────────────────────────────────────────────────────────────

∸∸-align-suc : ∀ m n' → (m ∸ 1) ∸ n' ≡ m ∸ suc n'
∸∸-align-suc zero n' = trans (0∸n≡0 n') (sym (0∸n≡0 (suc n')))
∸∸-align-suc (suc m') n' = sym (suc∸suc m' n')

-- ────────────────────────────────────────────────────────────────────
-- §6. suc∸1-form（x 形分裂）+ ∸-to-+（∸ 到加法反演——对 n 归纳）
-- ────────────────────────────────────────────────────────────────────

open import Data.Sum using (_⊎_; inj₁; inj₂)

suc∸1-form : ∀ x → suc (x ∸ 1) ≡ x ⊎ x ≡ 0
suc∸1-form zero = inj₂ refl
suc∸1-form (suc x') = inj₁ refl

∸-to-+ : ∀ m n o → m ∸ n ≡ o → n ≤ m → m ≡ n + o
∸-to-+ m zero o eq _ = trans eq refl
∸-to-+ (suc m') (suc n') o eq (s≤s n'≤m') =
  cong suc (∸-to-+ m' n' o (trans (sym (suc∸suc m' n')) eq) n'≤m')
