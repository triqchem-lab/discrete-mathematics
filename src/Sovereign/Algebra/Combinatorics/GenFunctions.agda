{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Combinatorics.GenFunctions
-- 生成函数的系数序列形（ℕ 系数域——Counting 同域衔接）——卷积乘积定理小例。
--
-- 数学背景：生成函数 F(x)=Σ fₙxⁿ 的纯系数承载（Series = ℕ → ℕ）；
--   乘积系数 = 离散卷积 (f⋆g)ₙ = Σᵢ fᵢ·gₙ₋ᵢ——"乘积=卷积"在此形是
--   定义相等（卷积即乘积系数的组合内容），Pascal 三案核对其计算面。
--
-- 核心原则：
-- 1. 系数序列形（ℕ 域——计数语义自然承载）
-- 2. 卷积 = 有限和递归（convSum——边界 n∸i 显式）
-- 3. 二项式系数族 = 生成函数系数（Pascal 递推的卷积表达）
-- 4. 禁浮点/超越——幂级数语义注记（log/exp 面立界）
--
-- 包含：Series/convSum/conv · binomS · 乘积=卷积 Pascal 三案 · 核对层 · 立界注记

module Sovereign.Algebra.Combinatorics.GenFunctions where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Algebra.Combinatorics.Counting using (binom)

-- §1 定义层（系数序列形）

Series : Set
Series = ℕ → ℕ

-- convSum f g n k = Σ_{i=0..k} f i * g (n ∸ i)（k ≤ n 截断和）
convSum : Series → Series → ℕ → ℕ → ℕ
convSum f g n zero    = f zero * g n
convSum f g n (suc k) = convSum f g n k + (f (suc k) * g (n ∸ suc k))

-- 卷积（= 乘积的系数形）
conv : Series → Series → ℕ → ℕ
conv f g n = convSum f g n n

-- §2 二项式系数族（Counting 衔接）

binomS : ℕ → Series
binomS m i = binom m i

-- §3 乘积=卷积 小例（Pascal 三案：(1+x)² 系数 = C(2,i)）
-- conv (binomS 1) (binomS 1) i ≡ binom 2 i（i=0,1,2 全 refl）

check-conv-0 : conv (binomS 1) (binomS 1) 0 ≡ binom 2 0
check-conv-0 = refl

check-conv-1 : conv (binomS 1) (binomS 1) 1 ≡ binom 2 1
check-conv-1 = refl

check-conv-2 : conv (binomS 1) (binomS 1) 2 ≡ binom 2 2
check-conv-2 = refl

-- 常值/单点核对
check-conv-const : conv (λ _ → 1) (λ _ → 1) 2 ≡ 3
check-conv-const = refl

check-conv-delta : conv (λ i → binom 0 i) (λ i → binom 0 i) 1 ≡ 0
check-conv-delta = refl

-- §4 立界注记（不设空壳签名）
-- (i) 一般卷积定理（GF3[X]×级数同构——依赖 Polynomials eval 同态，衔接批）
-- (ii) Pascal 递推的卷积一般形（∀ i ≤ m+n——三案外的全称形）
-- (iii) 幂级数语义（log/exp 面——禁超越纪律下为代数幂形式，深件立界）

