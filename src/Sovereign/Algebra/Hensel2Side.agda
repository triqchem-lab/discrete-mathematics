--------------------------------------------------------------------------------
-- | Sovereign.Algebra.Hensel2Side
-- 2 侧 Hensel 分类：x² ≡ 1 (mod 2^k) 的解结构。
--
-- 数学背景（与 Hensel3Side 同构、但有本质差异）：
--   3 侧：3∣x²∸1 → 3∣(x∸1) ⊎ 3∣suc(x)（二分，素性直接收缩）。
--   2 侧：二分对 2 的幂不成立（x=2¹⁵+1 反例）——正确结构是「四分」：
--     x² ≡ 1 (mod 2^k) (k≥3) ⟺ x ≡ ±1 或 ±(1+2^(k-1)) (mod 2^k)，恰 4 解。
--   论证骨架：
--     (1) x 偶 → x²∸1 奇 → 2^k ∤ x²∸1（k≥1），故解必奇。
--     (2) x 奇 → x∸1 与 suc x 均偶且差 2 → 恰一个被 4 整除、
--         另一个 ≡ 2 (mod 4)（即 2-adic 赋值恰 1）。
--     (3) 赋值恰 1 的因子「除一次」：2^k ∣ a·b ∧ 2∥a → 2^(k-1) ∣ b。
--     (4) 剩余幂次经素性二分（相邻互素）落到 x∸1 或 suc x 上。
--
-- 本模块当前闭合：pow2、two-odd-branch（2^k∣偶无解）、素性二分迭代引理。
--------------------------------------------------------------------------------

{-# OPTIONS --rewriting --guardedness #-}

module Sovereign.Algebra.Hensel2Side where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _≤_; _%_; s≤s; z≤n)
open import Data.Nat.Divisibility using (_∣_; divides; ∣1⇒≡1; 1∣_; ∣-refl; ∣⇒≤; ∣-trans; m∣m*n; n∣m*n; ∣m+n∣n⇒∣m; _∣?_)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor; coprime?)
open import Data.Nat.Properties using (*-suc; *-comm; *-zeroʳ; *-identityʳ; *-assoc; ≤-antisym; m≤m+n; ≤-trans; ≤-reflexive; 1+n≢n; suc-injective; _≟_; ≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

--------------------------------------------------------------------------------
-- §1. 2 的幂
--------------------------------------------------------------------------------

pow2 : ℕ → ℕ
pow2 zero = 1
pow2 (suc k) = 2 * pow2 k

--------------------------------------------------------------------------------
-- §2. 相邻互素与 2 的整除基础件
--------------------------------------------------------------------------------

-- 相邻互素：d∣a ∧ d∣suc(a) → d∣1（suc a 定义性 = 1 + a，经 ∣m+n∣n⇒∣m）
coprime-suc-a : ∀ a → Coprime a (suc a)
coprime-suc-a a (d∣a , d∣suc-a) = ∣1⇒≡1 (∣m+n∣n⇒∣m d∣suc-a d∣a)

-- Coprime 的参数对称（定义形状对称，交换字段即可）
coprime-2-a : ∀ a → Coprime a 2 → Coprime 2 a
coprime-2-a a c (d∣2 , d∣a) = c (d∣a , d∣2)

-- 2 ∣ pow2 (suc k)（定义性：pow2 (suc k) = 2 * pow2 k）
2∣pow2-suc : ∀ k → 2 ∣ pow2 (suc k)
2∣pow2-suc k = m∣m*n {m = 2} (pow2 k)

--------------------------------------------------------------------------------
-- §3. 素性迭代引理（2 侧核心收缩，仿 Hensel3Side 的 core）
--   pow2 k ∣ a·b ∧ Coprime a 2 → pow2 k ∣ b
--   对 k 归纳：suc 层先经 coprime-divisor 剥掉一个 2，再递归剩余幂次
--------------------------------------------------------------------------------

-- 半幂剥离：2·pow2 k ∣ a·b → pow2 k ∣ a·b（经 divides 字段 + *-assoc 重排）
pow2-half : ∀ k a b → 2 * pow2 k ∣ a * b → pow2 k ∣ a * b
pow2-half k a b (divides q eq) = divides (q * 2) (trans eq (sym (*-assoc q 2 (pow2 k))))

--------------------------------------------------------------------------------
-- §3. irred2：2 的整除分类（与 irred3 同构的四值判定器）
--   d ∣ 2 → d ≡ 1 ⊎ d ≡ 2（d=0 封闭 clash / d≥3 经 ∣⇒≤ 与 ≤⇒≤ᵇ）
--------------------------------------------------------------------------------

zero-2 : zero ∣ 2 → zero ≡ 2
zero-2 (divides q eq) = sym (trans eq (*-zeroʳ q))

zero-2-clash : 2 ≡ zero → ⊥
zero-2-clash ()

irred2 : ∀ d → d ∣ 2 → d ≡ 1 ⊎ d ≡ 2
irred2 d h with ∣⇒≤ h
... | dle with d ≟ zero
...   | yes d0 = ⊥-elim (zero-2-clash (sym (zero-2 (subst (λ w → w ∣ 2) d0 h))))
...   | no nd0 with d ≟ 1
...     | yes d1 = inj₁ d1
...     | no nd1 with d ≟ 2
...       | yes d2 = inj₂ d2
...       | no nd2 with d
...         | zero = ⊥-elim (nd0 refl)
...         | suc zero = ⊥-elim (nd1 refl)
...         | suc (suc zero) = ⊥-elim (nd2 refl)
...         | suc (suc (suc m)) = ⊥-elim (≤⇒≤ᵇ (≤-trans (s≤s (s≤s (s≤s z≤n))) dle))

--------------------------------------------------------------------------------
-- §4. 奇性传递链：¬2∣a → Coprime d 2 → div-pow2 → Coprime a (pow2 k)
--------------------------------------------------------------------------------

-- ¬2∣d → Coprime d 2（irred2 分类：d∣2 → d≡1 ✓ / d≡2 → 2∣d 矛盾）
coprime-d-2 : ∀ d → ¬ (2 ∣ d) → Coprime d 2
coprime-d-2 d nt2 {e} (e∣d , e∣2) with irred2 e e∣2
...   | inj₁ e≡1 = e≡1
...   | inj₂ e≡2 = ⊥-elim (nt2 (subst (λ w → w ∣ d) e≡2 e∣d))

-- d ∣ 2^k → d ≡ 1 ⊎ 2 ∣ d（对 k 归纳；suc 层经 coprime-divisor 剥一个 2）
div-pow2 : ∀ k d → d ∣ pow2 k → d ≡ 1 ⊎ 2 ∣ d
div-pow2 zero d h = inj₁ (∣1⇒≡1 h)
div-pow2 (suc k) d h with 2 ∣? d
...   | yes t = inj₂ t
...   | no nt2 = inj₁-sum
      where
        rec = div-pow2 k d (coprime-divisor (coprime-d-2 d nt2) h)
        inj₁-sum : d ≡ 1 ⊎ 2 ∣ d
        inj₁-sum with rec
        ...   | inj₁ e = inj₁ e
        ...   | inj₂ t2 = ⊥-elim (nt2 t2)



-- ¬2∣a → Coprime a (pow2 k)（经 div-pow2 分类）
coprime-a-pow2 : ∀ k a → ¬ (2 ∣ a) → Coprime a (pow2 k)
coprime-a-pow2 k a nt2 {e} (e∣a , e∣pow2) with div-pow2 k e e∣pow2
...   | inj₁ e≡1 = e≡1
...   | inj₂ 2∣e = ⊥-elim (nt2 (∣-trans 2∣e e∣a))

--------------------------------------------------------------------------------
-- §5. 素性迭代主引理（强化假设版，coprime-divisor 一步收缩）
--------------------------------------------------------------------------------

pow2-∣-iter : ∀ k a b → Coprime a (pow2 k) → pow2 k ∣ a * b → pow2 k ∣ b
pow2-∣-iter k a b c h = coprime-divisor (coprime-2-a-aux k a c) h
  where coprime-2-a-aux : ∀ k a → Coprime a (pow2 k) → Coprime (pow2 k) a
        coprime-2-a-aux k a c (d∣pow2 , d∣a) = c (d∣a , d∣pow2)

--------------------------------------------------------------------------------
-- §6. 奇偶两侧收缩（四分的数学核心）
--   奇 a：pow2 k ∣ a·suc(a) → pow2 k ∣ suc(a)（a 与 pow2 k 互素，iter 直接收缩）
--   偶 a：pow2 k ∣ a·suc(a) → pow2 k ∣ a（suc(a) 奇，与 pow2 k 互素，同上）
--   ——两引理合取即「赋值落到相邻 pair 的某一侧」，是 mod-4 赋值分析的代数核心
--------------------------------------------------------------------------------

2∣1-clash : 2 ∣ 1 → ⊥
2∣1-clash (divides zero ())            -- 1 ≡ 0 封闭 clash
2∣1-clash (divides (suc zero) ())      -- 1 ≡ 2 封闭 clash
2∣1-clash (divides (suc (suc q)) ())   -- 1 ≡ (2+q)·2 深度 clash

two-odd-b : ∀ k a → ¬ (2 ∣ a) → pow2 k ∣ a * suc a → pow2 k ∣ suc a
two-odd-b k a nt2 h = pow2-∣-iter k a (suc a) (coprime-a-pow2 k a nt2) h

two-even-a : ∀ k a → 2 ∣ a → pow2 k ∣ a * suc a → pow2 k ∣ a
two-even-a k a h2∣a h = pow2-∣-iter k (suc a) a (coprime-suc-pow2 h2∣a) (subst (λ w → pow2 k ∣ w) (*-comm a (suc a)) h)
  where
    -- suc a 奇（a 偶）→ Coprime (suc a) (pow2 k)：需 ¬2∣suc a
    -- a 偶 → suc a 奇：2∣suc a ∧ 2∣a → 2∣suc a ∸ a = 1 → 1 ≡ 2 clash
    coprime-suc-pow2 : 2 ∣ a → Coprime (suc a) (pow2 k)
    coprime-suc-pow2 h2∣a = coprime-a-pow2 k (suc a) (suc-a-odd h2∣a)
      where
        suc-a-odd : 2 ∣ a → ¬ (2 ∣ suc a)
        suc-a-odd h2∣a (divides q eq) = 2∣1-clash (∣m+n∣n⇒∣m (divides q eq) h2∣a)
