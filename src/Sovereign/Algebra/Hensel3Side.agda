{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Hensel3Side
-- 3 侧分类：x² ≡ 1 (mod 177147 = 3¹¹) ⟹ 177147 ∣ x∸1 或 177147 ∣ suc x
--
-- 数学背景：奇素数幂 p^k 上 x²≡1 只有 ±1 两根（gcd(x−1,x+1) ∣ 2 与 p 互素）。
--   恰 8 论证的第 1 件（2 侧 4 根分类另册，需 2-adic 赋值）。
--
-- 路线 A（采用）：coprime-divisor 二分——3∣suc x 判定分两侧，各经核心引理
--   （d∣3^k → d≡1 ⊎ 3∣d，对 k 归纳 + coprime? 收缩）建 Coprime。
-- 路线 B（备选）：10 步塔合成——件多链长未采用。
--
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Hensel3Side where

open import Data.Nat using (ℕ; zero; suc; _*_; _+_; _∸_; _≤_; s≤s; z≤n; ≤-antisym)
open import Data.Nat.Divisibility
  using (_∣_; divides; ∣1⇒≡1; ∣-refl; ∣⇒≤; ∣m+n∣n⇒∣m; ∣-trans; n∣m*n; m∣m*n)
open import Data.Nat.Divisibility using (_∣?_)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor; coprime?)
open import Data.Nat.Properties using (*-suc; *-comm; *-zeroʳ; *-identityʳ; +-identityʳ; 1+n≢n; suc-injective; ≤-antisym; m≤m+n; ≤-trans; m≤n⇒m≤1+n; ≤⇒≤ᵇ; ≤-reflexive; +-cancelˡ-≤)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; trans; subst)
open import Data.Nat.Properties using (_≟_)

--------------------------------------------------------------------------------
-- §1. 3 的幂
--------------------------------------------------------------------------------

pow3 : ℕ → ℕ
pow3 zero = 1
pow3 (suc k) = 3 * pow3 k

--------------------------------------------------------------------------------
-- §2. irred3：d ∣ 3 → d ≡ 1 ⊎ d ≡ 3
--     （d ≤ 3 四值判定器穷举——0 由封闭 clash、2 由 2∣?3 判定器、
--      3 由 3∣?3 判定器——零 ≤ 模式，绕开 primHComp 陷阱）
--------------------------------------------------------------------------------

zero-3 : zero ∣ 3 → zero ≡ 3
zero-3 (divides q eq) = sym (trans eq (*-zeroʳ q))

-- 闭式 clash 辅助件（模式位 () 对封闭数等式有效）
zero-3-clash : 3 ≡ zero → ⊥
zero-3-clash ()
two-3-clash : 2 ≡ 3 → ⊥
two-3-clash ()
three-4-clash : 4 ≡ 3 → ⊥
three-4-clash ()

four-∣3 : 4 ∣ 3 → ⊥
four-∣3 (divides zero ())
four-∣3 (divides (suc zero) ())
four-∣3 (divides (suc (suc q)) ())

parity23 : ¬ (2 ∣ 3)
parity23 (divides zero ())                    -- 3 ≡ 0 · 2 封闭 clash
parity23 (divides (suc zero) ())              -- 3 ≡ 1 · 2 = 2 封闭 clash
parity23 (divides (suc (suc zero)) ())        -- 3 ≡ 2 · 2 = 4 封闭 clash（four-form 的 ≤ 链由此消解）
parity23 (divides (suc (suc (suc q))) ())     -- 3 ≡ (3+q) · 2 归约 ≥ 6 深度 clash


irred3 : ∀ d → d ∣ 3 → d ≡ 1 ⊎ d ≡ 3
irred3 d h with ∣⇒≤ h
... | dle with d ≟ zero
...   | yes d0 = ⊥-elim (zero-3-clash (sym (zero-3 (subst (λ w → w ∣ 3) d0 h))))
...   | no nd0 with d ≟ 1
...     | yes d1 = inj₁ d1
...     | no nd1 with d ≟ 2
...       | yes d2 = ⊥-elim (parity23 (subst (λ w → w ∣ 3) d2 h))
...       | no nd2 with d ≟ 3
...         | yes d3 = inj₂ d3
...         | no nd3 with d
...           | zero = ⊥-elim (nd0 refl)
...           | suc zero = ⊥-elim (nd1 refl)
...           | suc (suc zero) = ⊥-elim (nd2 refl)
...           | suc (suc (suc zero)) = ⊥-elim (nd3 refl)
...           | suc (suc (suc (suc m))) = ⊥-elim (≤⇒≤ᵇ (≤-trans (s≤s (s≤s (s≤s (s≤s z≤n)))) dle))


--------------------------------------------------------------------------------
-- §3. 核心引理：d ∣ 3^k → d ≡ 1 ⊎ 3 ∣ d
--     （Prime-free：coprime? 判定 + irred3 收缩，对 k 归纳）
--------------------------------------------------------------------------------

core : ∀ k d → d ∣ pow3 k → d ≡ 1 ⊎ 3 ∣ d
core zero d h = inj₁ (∣1⇒≡1 h)
core (suc k) d h with 3 ∣? d
...   | yes t = inj₂ t
...   | no nt3 = inj₁-sum
      where
        h2 : d ∣ 3 * pow3 k
        h2 = h
        copr : Coprime d 3
        copr {e} (e∣d , e∣3) with irred3 e e∣3
        ...   | inj₁ e≡1 = e≡1
        ...   | inj₂ e≡3 = ⊥-elim (nt3 (subst (λ w → w ∣ d) e≡3 e∣d))
        inner = core k d (coprime-divisor copr h2)
        inj₁-sum : d ≡ 1 ⊎ 3 ∣ d
        inj₁-sum with inner
        ...   | inj₁ e = inj₁ e
        ...   | inj₂ t3 = ⊥-elim (nt3 t3)

--------------------------------------------------------------------------------
-- §4. 乘积桥：(x ∸ 1) * suc x ≡ x * x ∸ 1
--------------------------------------------------------------------------------

px : ∀ x → (x ∸ 1) * suc x ≡ x * x ∸ 1
px zero = refl
px (suc x') =
  trans (*-comm x' (suc (suc x')))
  (trans refl
  (cong (λ w → x' + w) (sym (*-suc x' x'))))

--------------------------------------------------------------------------------
-- §5. 三分判定与 3 侧二分定理
--     3 ∣ a·b → 3∣a ⊎ 3∣b（3 的素性经 irred3）；
--     3∣x²∸1 → 3∣(x∸1) ⊎ 3∣suc(x)（经 px 乘积桥）
--------------------------------------------------------------------------------

-- Coprime 3 a 由 ¬(3∣a) 构造：e∣3 → e≡1（inj₁）或 e≡3 → 3∣a 与 nt3 矛盾
coprime-3 : ∀ a → ¬ (3 ∣ a) → Coprime 3 a
coprime-3 a nt3 {e} (e∣3 , e∣a) with irred3 e e∣3
...   | inj₁ e≡1 = e≡1
...   | inj₂ e≡3 = ⊥-elim (nt3 (subst (λ w → w ∣ a) e≡3 e∣a))

three-dichotomy : ∀ a b → 3 ∣ a * b → 3 ∣ a ⊎ 3 ∣ b
three-dichotomy a b h with 3 ∣? a
...   | yes t = inj₁ t
...   | no nt3 = inj₂ (coprime-divisor (coprime-3 a nt3) h)

three-side : ∀ x → 3 ∣ x * x ∸ 1 → 3 ∣ x ∸ 1 ⊎ 3 ∣ suc x
three-side x h = three-dichotomy (x ∸ 1) (suc x) (subst (λ w → 3 ∣ w) (sym (px x)) h)
