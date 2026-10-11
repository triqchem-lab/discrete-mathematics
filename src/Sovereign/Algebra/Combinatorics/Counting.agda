{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Combinatorics.Counting
-- 组合计数基础：二项式系数（Pascal 递归形）与计数恒等式
--
-- 数学背景：C(n,k) 的 Pascal 递归定义（免阶乘/除法——纯 ℕ 递归）：
--   C(n+1,k+1) = C(n,k) + C(n,k+1)，边缘 C(n,0)=C(n,n)=1，越界 C(n,k)=0 (k>n)。
-- 核心恒等式：Pascal 恒等式（定义形）/ 边缘律 / 越界归零 / 系数行和 ΣₖC(n,k)=2ⁿ
--   / 多重组合（星棒系数）C(n+k−1,k)。
--
-- 核心原则：
-- 1. Pascal 递归形定义（与阶乘形定义等价但构造性零除法）
-- 2. 全部恒等式构造性证明（归纳 + ℕ 代数链，零 postulate）
-- 3. 多重组合 = 星棒系数包装——定义层形，计数语义（分拆数）注记
-- 4. 二项式定理一般形（(x+y)ⁿ 展开）：重排链立界（附录 14 面）——本件交付
--    系数恒等式骨干，展开定理注记 §5（不设空壳签名）
-- 5. 复用零重证：计数语义锚 = Foundation.Finiteness.Pigeonhole.pigeonhole-iff
--    / _PFT.SeqRepeats（本件不 import——注记引用，语义面衔接）
--
-- 包含：binom/Pascal · 边缘律 · 越界归零 · binom-n-1 · pow2 · rs/行和定理
--       · multiset（星棒）· Fin 核对 ×4

module Sovereign.Algebra.Combinatorics.Counting where

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤_)
open import Data.Nat.Properties using
  (≤-step; ≤-pred; ≤-refl; +-assoc; +-comm; +-identityʳ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂)

------------------------------------------------------------------------
-- §1 基础件层：Pascal 递归形二项式系数
------------------------------------------------------------------------

-- C(n,k)：Pascal 三角递归——四个构造子案互不重叠、全域覆盖
binom : ℕ → ℕ → ℕ
binom zero    zero    = 1
binom zero    (suc k) = 0
binom (suc n) zero    = 1
binom (suc n) (suc k) = binom n k + binom n (suc k)

-- Pascal 恒等式（定义形——本件设计使然）
pascal : ∀ n k → binom (suc n) (suc k) ≡ binom n k + binom n (suc k)
pascal n k = refl

------------------------------------------------------------------------
-- §2 主引理层：边缘律 / 越界归零 / 退化值
------------------------------------------------------------------------

-- 边缘律一：C(n,0) = 1
binom-n-0 : ∀ n → binom n 0 ≡ 1
binom-n-0 zero    = refl
binom-n-0 (suc n) = refl

-- 边缘律二：C(0,k+1) = 0
binom-0-suc : ∀ k → binom 0 (suc k) ≡ 0
binom-0-suc k = refl

-- 越界归零：k > n ⟹ C(n,k) = 0（对 n 归纳——归纳步两项同消）
binom-lt : ∀ n k → n < k → binom n k ≡ 0
binom-lt zero    (suc k) _          = refl
binom-lt (suc n) (suc k) nk         =
  -- (A+B) = 0+0 = 0 [两项 IH + 零加]
  trans (cong₂ _+_ (binom-lt n k (≤-pred nk))
        (binom-lt n (suc k) (≤-step (≤-pred nk)))) refl

-- 边缘律三：C(n,n) = 1（归纳——越界项归零 + 右单位）
binom-n-n : ∀ n → binom n n ≡ 1
binom-n-n zero    = refl
binom-n-n (suc n) =
  -- C(n+1,n+1) = C(n,n) + C(n,n+1) = 1 + 0 = 1 [IH + 越界 + 右单位]
  trans (cong₂ _+_ (binom-n-n n) (binom-lt n (suc n) ≤-refl)) (+-identityʳ 1)

-- 退化值：C(n,1) = n（归纳——1+n 定义相等 suc n）
binom-n-1 : ∀ n → binom n 1 ≡ n
binom-n-1 zero    = refl
binom-n-1 (suc n) =
  -- C(n+1,1) = C(n,0) + C(n,1) = 1 + n = suc n [边缘一 + IH + 定义相等]
  trans (cong₂ _+_ (binom-n-0 n) (binom-n-1 n)) refl

------------------------------------------------------------------------
-- §3 组合层：行和定理（加法原理形）Σₖ C(n,k) = 2ⁿ
------------------------------------------------------------------------

-- 2 的幂（加倍递归）
pow2 : ℕ → ℕ
pow2 zero    = 1
pow2 (suc n) = pow2 n + pow2 n

-- 行前缀和：rs n m = Σ_{k=0..m} C(n,k)（左累积）
rs : ℕ → ℕ → ℕ
rs n zero    = binom n zero
rs n (suc k) = rs n k + binom n (suc k)

rs-suc : ∀ n k → rs n (suc k) ≡ rs n k + binom n (suc k)
rs-suc n k = refl

-- 桥引理：rs n 0 ≡ 1 / rs n 1 ≡ 1+n（binom 变元首参 stuck——须引理桥接）
rs-n-0 : ∀ n → rs n 0 ≡ 1
rs-n-0 n = binom-n-0 n

rs-n-1 : ∀ n → rs n 1 ≡ 1 + n
rs-n-1 n = cong₂ _+_ (binom-n-0 n) (binom-n-1 n)

-- 行尾即整行：rs n (suc n) = rs n n（越界项归零 + 右单位）
rs-n-sucn : ∀ n → rs n (suc n) ≡ rs n n
rs-n-sucn n =
  -- Σ(n,k≤n+1) = Σ(n,k≤n) + C(n,n+1) = Σ + 0 = Σ [越界 + 右单位]
  trans (rs-suc n n)
    (trans (cong₂ _+_ refl (binom-lt n (suc n) ≤-refl)) (+-identityʳ (rs n n)))

-- 中间两项换位（rearrange 4 元）：(a+b)+(c+d) ≡ (a+d)+(b+c)
mid2swap : ∀ a b c d → (a + b) + (c + d) ≡ (a + d) + (b + c)
-- 四步链：右结合 → 中项交换 → 左收 [每步一引理]
mid2swap a b c d =
  trans (+-assoc a b (c + d))
    (trans (cong (a +_) (sym (+-assoc b c d)))
      (trans (cong (a +_) (+-comm (b + c) d))
        (sym (+-assoc a d (b + c)))))

-- Pascal 行移位：Σ_{k≤m+1} C(n+1,k) = Σ_{k≤m+1} C(n,k) + Σ_{k≤m} C(n,k)
-- （对 m 归纳——递推步 = 中间换位）
rs-pascal : ∀ n k → rs (suc n) (suc k) ≡ rs n (suc k) + rs n k
rs-pascal n zero    =
  -- 1 + rs n 1 ≡ rs n 1 + 1 ≡ rs n 1 + rs n 0 [交换 + 桥引理]
  trans (+-comm 1 (rs n 1)) (cong (rs n 1 +_) (sym (rs-n-0 n)))
rs-pascal n (suc k) =
  -- (IH 形) + (C(n,k+1)+C(n,k+2)) → 中间换位 → 目标形
  trans (cong₂ _+_ (rs-pascal n k) refl)
    (mid2swap (rs n (suc k)) (rs n k) (binom n (suc k)) (binom n (suc (suc k))))

-- 行和定理（加法原理）：Σₖ C(n,k) = 2ⁿ
binom-row-sum : ∀ n → rs n n ≡ pow2 n
binom-row-sum zero    = refl
binom-row-sum (suc n) =
  -- Σ(n+1,k≤n+1) = Σ(n,k≤n+1) + Σ(n,k≤n) = Σ(n,k≤n) + Σ(n,k≤n) = 2·2ⁿ
  trans (rs-pascal n n)
    (trans (cong₂ _+_ (rs-n-sucn n) refl)
      (trans (cong₂ _+_ (binom-row-sum n) (binom-row-sum n)) refl))

------------------------------------------------------------------------
-- §4 基础件层（续）：多重组合（星棒系数）
------------------------------------------------------------------------

-- 多重组合数 = 星棒系数 C(n+k-1, k)——n 类取 k 允重复的组合数
-- （计数语义：分拆/多重集面；定义层形，语义证明立界 §5）
multiset : ℕ → ℕ → ℕ
multiset n k = binom (n + k ∸ 1) k

multiset-0 : ∀ n → multiset n 0 ≡ 1
multiset-0 n = binom-n-0 (n + 0 ∸ 1)

-- 退化值：n 类取 1 = n（n+1∸1 = n 定义相等）
multiset-1 : ∀ n → multiset n 1 ≡ n
multiset-1 n = trans (cong (λ m → binom (m ∸ 1) 1) (+-comm n 1)) (binom-n-1 n)

------------------------------------------------------------------------
-- §5 核对层：Fin 级具体值（refl 级跨通道对账）
------------------------------------------------------------------------

-- C(5,2) = 10 [Pascal 递归直接归约]
check-binom-52 : binom 5 2 ≡ 10
check-binom-52 = refl

-- C(4,2) = 6
check-binom-42 : binom 4 2 ≡ 6
check-binom-42 = refl

-- 行和核对：Σₖ C(4,k) = 16 = 2⁴
check-row-sum-4 : rs 4 4 ≡ pow2 4
check-row-sum-4 = refl

-- Pascal 值核对：C(5,3) = C(4,2) + C(4,3) = 6 + 4
check-pascal-val : binom 5 3 ≡ binom 4 2 + binom 4 3
check-pascal-val = refl

------------------------------------------------------------------------
-- §6 立界注记（诚实边界——不设空壳签名）
-- (i) 二项式定理一般形：(x+y)ⁿ = Σₖ C(n,k)·xᵏ·yⁿ⁻ᵏ（ℕ 版 ~100-150 行
--     重排链——附录 14 rearrange 面；系数骨干即本件 rs/pascal/mid2swap）；
-- (ii) binom 对称律 C(n,k) ≡ C(n,n∸k)（∸ 代数链 ~40 行）；
-- (iii) multiset 计数语义（多重集/分拆双射）；
-- (iv) 乘法原理一般形（积空间计数——接 DiscreteProbability 批）。
-- 语义锚（复用零重证）：Finiteness.Pigeonhole.pigeonhole-iff（:62）
--   / _PFT.SeqRepeats（组合计数的鸽巢/Tarski 面）。
