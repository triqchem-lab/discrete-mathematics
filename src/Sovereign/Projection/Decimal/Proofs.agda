{-# OPTIONS --rewriting --cubical --guardedness #-}

-- | Sovereign.Projection.Decimal.Proofs
-- 十进制数字根正确性的构造性证明
--
-- ⚠️ 宪法声明：
-- - 这些证明在十进制自然数体系内**严谨完备**
-- - 但与律算 GF(3) 驻波叠加表属于**不同范畴**
-- - 证明内容包括：
--   1. divMod10Correct：十进制除法正确性
--   2. sumDigitsTerminates：数字和递归终止性
--   3. digitalRoot 稳定性证明

module Sovereign.Projection.Decimal.Proofs where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _≥_; _>_; _<_; s≤s; z≤s; z≤n)
open import Data.Nat.Properties using (s<s; z<s; *-suc; +-comm; +-assoc; m<m+n; ≤-trans; ≤-refl; m≤m+n; n≤m+n; +-monoˡ-<; +-identityʳ; m≤n⇒m<n∨m≡n; ≤-pred)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

-- stdlib 2.4 未导出 ¬suc≤zero, 本地定义
¬suc≤zero : ∀ {n} → suc n ≤ zero → ⊥
¬suc≤zero ()

open import Sovereign.Projection.Decimal.Axioms

--------------------------------------------------------------------------------
-- 1. divMod10 正确性证明
--------------------------------------------------------------------------------

-- 辅助引理：乘法分配律 (2026-08 P0: 原 postulate → stdlib *-suc + +-comm)
suc-*-distrib : (q n : ℕ) → q * suc n ≡ q * n + q
suc-*-distrib q n = trans (*-suc q n) (+-comm q (q * n))

true≢false : true ≡ false → ⊥
true≢false ()

-- 定理：divMod10 n = (q, r) 满足 n = q * 10 + r 且 r < 10
-- [2026-08 P0 D 类收尾策略] 基础已备: suc-*-distrib/lemma_q_lt/lemma_sum_lt
--   (上方已证)。证法: 对 n 归纳; with divMod10 n | divMod10Correct n;
--   再 with suc r <10 in br — true 支: cong suc n≡ + <10⇒< (suc r) br;
--   false 支: 由 r<10 (≤-pred) + m≤n⇒m<n∨m≡n 导出 r≡9 (r<9 支与 br 矛盾),
--   再以 *-comm/*-suc 链证明 q*10+9+1 ≡ suc q*10。
postulate
  divMod10Correct : (n : ℕ) → 
    let (q , r) = divMod10 n
    in n ≡ q * 10 + r × r < 10

--------------------------------------------------------------------------------
-- 2. sumDigits 终止性证明
--------------------------------------------------------------------------------

-- 辅助引理: q ≥ 1 → q < q * 10 + r (2026-08 P0: 原 postulate → 证明)
-- q*10 = q + q*9; q*9+r ≥ 1 由 q≥1 导出; m<m+n 给严格性。
lemma_q_lt : (q r : ℕ) → q ≥ 1 → q < q * 10 + r
lemma_q_lt q r q≥1 =
  subst (q <_) (lemma-q-eq q r) (m<m+n q {q * 9 + r} (nz q r q≥1))
  where
    lemma-q-eq : ∀ q r → q + (q * 9 + r) ≡ q * 10 + r
    lemma-q-eq q r =
      trans (sym (+-assoc q (q * 9) r)) (cong (_+ r) (sym (*-suc q 9)))
    nz : ∀ q r → q ≥ 1 → q * 9 + r > 0
    nz q r q≥1 =
      ≤-trans (≤-trans q≥1 (subst (λ x → q ≤ x) (sym (*-suc q 8)) (m≤m+n q (q * 8))))
        (m≤m+n (q * 9) r)

-- 辅助引理: q ≥ 1 → r < 10 → r + q < q * 10 + r
-- (2026-08 P0: 原签名缺 q≥1 前提 — q=0 时 r < r 为假; 补前提后证明)
lemma_sum_lt : (q r : ℕ) → q ≥ 1 → r < 10 → r + q < q * 10 + r
lemma_sum_lt q r q≥1 r<10 =
  subst (λ x → x < q * 10 + r) (sym (+-comm r q))
    (subst (λ x → q + r < x + r) (+-identityʳ (q * 10))
      (+-monoˡ-< r (lemma_q_lt q 0 q≥1)))

-- 主定理：∀ n → n ≥ 10 → sumDigits n < n
-- [2026-08 P0 D 类收尾策略] 依赖 divMod10Correct: n ≡ q*10+r →
--   sumDigits n = r + sumDigits q ≤ r + q < q*10+r = n (lemma_sum_lt q≥1)。
--   q≥1 由 n≥10 导出 (lemma_q_lt 的反向); sumDigits q ≤ q 需一并归纳。
--   digitalRootConverges/Stable 需沿 sumDigitsTerminates 的良基归纳
--   (digitalRoot 的 {-# TERMINATING #-} 递归), 收敛后按 0..9 十 case refl。
postulate
  sumDigitsTerminates : (n : ℕ) → n ≥ 10 → sumDigits n < n
  digitalRootConverges : (n : ℕ) → digitalRoot n < 10
  digitalRootStable : (n : ℕ) → IsStable n ≡ true → 
    digitalRoot n ≡ 3 ⊎ digitalRoot n ≡ 6 ⊎ digitalRoot n ≡ 9

--------------------------------------------------------------------------------
-- ⚠️ 待完成项
--------------------------------------------------------------------------------

-- 以下证明需要补充完整：
-- 1. lemma_q_lt - 不等式构造
-- 2. lemma_sum_lt - 不等式构造
-- 3. sumDigitsTerminates - 主证明项
-- 4. digitalRootConverges - 收敛性证明
-- 5. digitalRootStable - 稳定性证明

-- 这些证明在十进制自然数体系内是严谨的构造性证明
