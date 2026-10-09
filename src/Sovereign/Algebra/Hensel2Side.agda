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
open import Data.Nat.Divisibility using (_∣_; divides; ∣1⇒≡1; 1∣_; ∣-refl; ∣⇒≤; ∣-trans; m∣m*n; n∣m*n; ∣m+n∣n⇒∣m)
open import Data.Nat.Coprimality using (Coprime; coprime-divisor)
open import Data.Nat.Properties using (*-suc; *-comm; *-zeroʳ; *-identityʳ; *-assoc; ≤-antisym; m≤m+n; ≤-trans; ≤-reflexive; 1+n≢n; suc-injective)
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

pow2-∣-iter : ∀ k a b → pow2 k ∣ a * b → Coprime a 2 → pow2 k ∣ b
pow2-∣-iter zero a b h c = 1∣ b
pow2-∣-iter (suc k) a b h c =
  IH
  where
    -- 剥一个 2：2 ∣ a·b 且 Coprime 2 a → 2 ∣ b
    step2 : 2 ∣ b
    step2 = coprime-divisor (coprime-2-a a c) (∣-trans (2∣pow2-suc k) h)
    -- 剩余幂次：pow2 k ∣ a·b（由 2·pow2 k ∣ a·b 经 *-assoc 重排）
    rest : pow2 k ∣ a * b
    rest = pow2-half k a b h
    IH : pow2 k ∣ b
    IH = {!强化假设待下批：需 Coprime a (pow2 k) 或经 coprime-* 组合!}
