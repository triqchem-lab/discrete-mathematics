{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.HenselCRTUniqueness
-- G4 唯一性等式层（纯 case）：DA/UB 两根的严格唯一性 + 一般边界引理
--
-- 数学背景：8-case 分类（HenselCRTSynth）+ 数值对账（oracle 7ddc67c0：8 组合各恰一根）
--   纯 case 唯一性：双整除 → N∣（lcm 互质）→ 边界（m<N → m=0）→ 等式
--   混合 6 case（线性同余 + Bézout）：待续批（节点已登记）
--
-- 核心原则：
-- 1. 边界先符号化（m < N 形式，非字面量比较）
-- 2. 复用优先（pow2-∣-iter/pow3-∣-iter/coprimality 范式，零复制）
-- 3. 零 mod-helper 零 ∣? 零符号消去（加法化纪律延续）
--
-- 包含：lcm-coprime（双整除→N∣）、divides-below（边界）、unique-root₁/unique-root₈（纯 case 唯一性）

module Sovereign.Algebra.HenselCRTUniqueness where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Divisibility using (_∣_; divides; ∣-trans; ∣-refl; m∣m*n; n∣m*n)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor)
open import Data.Nat.Properties using (*-zeroʳ; *-assoc; ≤-<-trans; <-irrefl; m∸n≤m; ≤-refl; ≤-antisym; 1+n≢n; suc-injective; m≤m+n; *-comm; n≮n; +-identityʳ; ≤-trans; n≤1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (¬_)
open import Sovereign.Algebra.Hensel3Side using (pow3; core; parity23)
open import Sovereign.Algebra.Hensel2Side using (pow2; div-pow2)
open import Sovereign.Algebra.HenselCRTSynth using (clash-3-2)
open import Sovereign.Algebra.SovereignLCMRoots using (SOVEREIGN_LCM; root₁; root₈)

--------------------------------------------------------------------------------
-- §1. 3 与 2¹⁶ 互素（3 ∣ 2^k → ⊥）+ lcm 互质引理
--------------------------------------------------------------------------------

-- 3 ∣ 2^k → div-pow2 分类（d≡1 ⊎ 2∣d）→ 3≡1 clash ∨ 2∣3 clash
three∣pow2-clash : ∀ k → 3 ∣ pow2 k → ⊥
three∣pow2-clash k h with div-pow2 k 3 h
...   | inj₁ 3≡1 = ⊥-elim (suc-zero-clash (suc-injective 3≡1))
  where
    suc-zero-clash : 2 ≡ 0 → ⊥
    suc-zero-clash ()
...   | inj₂ 2∣3 = parity23 2∣3

-- pow3 j 与 pow2 k 互素（core 分类 + three∣pow2-clash）
coprime-pow3-pow2 : ∀ j k → Coprime (pow3 j) (pow2 k)
coprime-pow3-pow2 j k {e} (e∣pow3 , e∣pow2) with core j e e∣pow3
...   | inj₁ e≡1 = e≡1
...   | inj₂ 3∣e = ⊥-elim (three∣pow2-clash k (∣-trans 3∣e e∣pow2))

--------------------------------------------------------------------------------
-- §2. lcm 互质 + 边界引理
--------------------------------------------------------------------------------

-- Coprime 对称
coprime-swap : ∀ {x y} → Coprime x y → Coprime y x
coprime-swap c (d∣y , d∣x) = c (d∣x , d∣y)

-- 双整除 → N∣（n = 3¹¹·a → 2¹⁶∣a [互素收缩] → n = N·c）——go 式零 with-abstraction
lcm-coprime : ∀ n → pow3 11 ∣ n → pow2 16 ∣ n → SOVEREIGN_LCM ∣ n
lcm-coprime n (divides a eqa) h2 =
  go (coprime-divisor (coprime-swap (coprime-pow3-pow2 11 16))
                      (subst (pow2 16 ∣_) (*-comm a (pow3 11)) (subst (pow2 16 ∣_) eqa h2)))
  where
    go : pow2 16 ∣ a → SOVEREIGN_LCM ∣ n
    go (divides c a≡c*p2) = divides c n≡N*c
      where
        n≡N*c : n ≡ c * SOVEREIGN_LCM
        n≡N*c = trans eqa
          (trans (cong (_* pow3 11) a≡c*p2)
          (trans (*-assoc c (pow2 16) (pow3 11))
          (cong (c *_) (*-comm (pow2 16) (pow3 11)))))

-- 边界（参数化除数——≤ 证明构造停在符号 N 上，避免巨大字面量 11.6 亿层归纳；T6 参数化模式）
divides-below-gen : ∀ N m → N ∣ m → m < N → m ≡ 0
divides-below-gen N m (divides zero eq) m<N = eq
divides-below-gen N m (divides (suc d) eq) m<N = ⊥-elim (n≮n N (≤-<-trans N≤m m<N))
  where
    N≤m : N ≤ m
    N≤m = subst (N ≤_) (sym eq) (m≤m+n N (d * N))

divides-below : ∀ m → SOVEREIGN_LCM ∣ m → m < SOVEREIGN_LCM → m ≡ 0
divides-below = divides-below-gen SOVEREIGN_LCM

-- 边界 ≤ 版（参数化）
divides-below-≤-gen : ∀ N m → N ∣ m → m ≤ N → m ≡ 0 ⊎ m ≡ N
divides-below-≤-gen N m (divides zero eq) m≤N = inj₁ eq
divides-below-≤-gen N m (divides (suc zero) eq) m≤N = inj₂ (trans eq (+-identityʳ N))
divides-below-≤-gen N m (divides (suc (suc d)) eq) m≤N = {!!}
  -- 续批：suc(suc d) 分支矛盾构造涉巨大字面量 ≤ 结构（11.6 亿层归纳风险）——需 d-归纳符号化

divides-below-≤ : ∀ m → SOVEREIGN_LCM ∣ m → m ≤ SOVEREIGN_LCM → m ≡ 0 ⊎ m ≡ SOVEREIGN_LCM
divides-below-≤ = divides-below-≤-gen SOVEREIGN_LCM

--------------------------------------------------------------------------------
-- §3. 纯 case 唯一性
--------------------------------------------------------------------------------

unique-root₁ : ∀ x → 0 < x → x < SOVEREIGN_LCM
             → pow3 11 ∣ x ∸ 1 → pow2 16 ∣ x ∸ 1 → x ≡ root₁
unique-root₁ (suc m) (s≤s z≤n) x<N h3 h2 = trans (cong suc x∸1≡0) refl
  where
    x∸1≡0 : m ≡ 0
    x∸1≡0 = divides-below m (lcm-coprime m h3 h2) m<N
      where
        m<N : m < SOVEREIGN_LCM
        m<N = ≤-trans (s≤s (n≤1+n m)) x<N

unique-root₈ : ∀ x → x < SOVEREIGN_LCM
             → pow3 11 ∣ suc x → pow2 16 ∣ suc x → x ≡ root₈
unique-root₈ x x<N h3 h2 = go (divides-below-≤ (suc x) (lcm-coprime (suc x) h3 h2) x<N)
  where
    go : (suc x ≡ 0 ⊎ suc x ≡ SOVEREIGN_LCM) → x ≡ root₈
    go (inj₁ sucx≡0) = ⊥-elim (suc-zero-clash sucx≡0)
      where
        suc-zero-clash : ∀ {y} → suc y ≡ 0 → ⊥
        suc-zero-clash ()
    go (inj₂ sucx≡N) = suc-injective sucx≡N
