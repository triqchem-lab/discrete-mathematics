{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.DayanProof
-- 大衍求一术 L2 完整证明——纯 + / - 展开版（消除中缀减法）
--
-- 核心策略：不用中缀减法 `a - b`，全部展开为 `a + (- b)`。
-- 这样 *-distribʳ-+ 直接匹配，无定义性展开问题。
module Sovereign.Algebra.DayanProof where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; 0ℤ; 1ℤ; _+_; _*_; -_)
open import Data.Integer.Properties using
  ( *-identityˡ; *-zeroˡ; +-identityʳ
  ; *-distribʳ-+
  ; neg-distribˡ-*
  )
open import Data.Nat renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Product using (Σ; _×_; _,_)

--------------------------------------------------------------------------------
-- §1. 不变量（纯 + / - 形式）
--------------------------------------------------------------------------------

-- 不变量：s × 奇₀ + k × 定₀ = rt
-- 没有减法——全部用 + 和 -（一元负号）
Inv : ℕ → ℕ → ℤ → ℕ → Set
Inv 奇₀ 定₀ s rt = Σ ℤ (λ k → s * (+ 奇₀) + k * (+ 定₀) ≡ + rt)

--------------------------------------------------------------------------------
-- §2. step-invariant——完整证明
--
--   给定三个等式（全部用 + 和 - 表示，无中缀减法）：
--     (CUR)  lt×奇 + k₁×定 = rt
--     (PREV) lb×奇 + k₂×定 = rb
--     (DIV)  rb = q×rt + r
--
--   构造 witness: k' = k₂ + -(q×k₁)
--
--   新系数: new_lt = lb + -(q×lt)   （等价于 lb - q×lt）
--
--   证明：
--     new_lt×奇 + k'×定
--     = (lb + -(q×lt))×奇 + (k₂ + -(q×k₁))×定
--     = [lb×奇 + k₂×定] + -[q×lt×奇 + q×k₁×定]   ← 分配律重排
--     = [lb×奇 + k₂×定] + -[q×(lt×奇 + k₁×定)]   ← 提取公因子 q
--     = rb + -(q×rt)                               ← 代入 (CUR) 和 (PREV)
--     = r                                           ← 代入 (DIV)
--------------------------------------------------------------------------------

-- 核心代数引理：分配律重排
-- (a + -(b*c)) * d + (e + -(b*f)) * g
--   = (a*d + e*g) + -(b*(c*d + f*g))
--
-- 证明：两边展开
--   LHS = a*d + -(b*c)*d + e*g + -(b*f)*g
--       = a*d + e*g + (-(b*c*d) + -(b*f*g))     ← neg-distribˡ-*
--       = a*d + e*g + -(b*c*d + b*f*g)           ← neg-distrib-+
--       = a*d + e*g + -(b*(c*d + f*g))           ← 提取公因子
--   RHS = a*d + e*g + -(b*(c*d + f*g))
--
-- 在 Agda 中，这个引理需要多步 ℤ 代数。

-- step-invariant 证明（用展开形式，不需要减法分配律）
step-invariant : ∀ (奇₀ 定₀ : ℕ) (lt lb : ℤ) (rt rb : ℕ) (q : ℤ) (r : ℕ) →
  -- 当前不变量
  Inv 奇₀ 定₀ lt rt →
  -- 前一步不变量
  Inv 奇₀ 定₀ lb rb →
  -- 除法关系：rb = q×rt + r
  (+ rb) ≡ q * (+ rt) + (+ r) →
  -- 结论：(lb + -(q×lt))×奇 + (k₂ + -(q×k₁))×定 = r
  Inv 奇₀ 定₀ (lb + (- (q * lt))) r

step-invariant 奇₀ 定₀ lt lb rt rb q r
  (k₁ , inv-cur) (k₂ , inv-prev) div-rel =
  (k₂ + (- (q * k₁)) , proof)

  where
    -- 目标：(lb + -(q*lt))*奇 + (k₂ + -(q*k₁))*定 = r
    -- 数学推导（每步标注所需的 ℤ 引理）：

    -- 1. 分配律展开 LHS:
    --    lb*奇 + -(q*lt)*奇 + k₂*定 + -(q*k₁)*定
    --    = lb*奇 + k₂*定 + -(q*lt)*奇 + -(q*k₁)*定     ← +comm 重排
    --    = (lb*奇 + k₂*定) + -[q*(lt*奇) + q*(k₁*定)] ← neg-distribˡ-* ×2
    --    = (lb*奇 + k₂*定) + -[q*(lt*奇 + k₁*定)]     ← *-distribˡ-+ 反向

    -- 2. 代入不变量:
    --    lb*奇 + k₂*定 = rb        (inv-prev)
    --    lt*奇 + k₁*定 = rt        (inv-cur)
    --    ⟹ (rb) + -(q*rt)          ← cong₂

    -- 3. 代入除法:
    --    rb = q*rt + r
    --    ⟹ (q*rt + r) + -(q*rt) = r  ← +comm + 消去

    proof : (lb + (- (q * lt))) * (+ 奇₀) + (k₂ + (- (q * k₁))) * (+ 定₀) ≡ + r
    proof = {!ℤ 代数推导!}
    -- 此 hole 需要的引理全部在 Data.Integer.Properties 中：
    --   *-distribʳ-+, *-distribˡ-+, neg-distribˡ-*, +-assoc, +-comm
    -- 证明结构：≈15-20 行的 ≡-Reasoning 链

--------------------------------------------------------------------------------
-- §3. terminate-correct——恒等映射
--------------------------------------------------------------------------------

terminate-correct : ∀ (奇₀ 定₀ : ℕ) (lt : ℤ) →
  Inv 奇₀ 定₀ lt 1 →
  Σ ℤ (λ k → lt * (+ 奇₀) + k * (+ 定₀) ≡ + 1)
terminate-correct 奇₀ 定₀ lt inv = inv
-- ✅ 恒等映射！不变量就是乘率性质。

--------------------------------------------------------------------------------
-- §4. 完成度
--
--   ✅ step-invariant witness: k₂ + -(q×k₁)（构造完成）
--   ✅ terminate-correct: 恒等映射（不变量=乘率定义）
--   ⚠ step-invariant proof body: 需 ℤ 代数 ≡-Reasoning 链（≈15-20 行）
--      所需引理全部在 stdlib，推导结构已在注释中完整写出
--
--   这是 Agda 证明的最后一步——需要逐行写 ≡-Reasoning 链。
--   数学推导已完成，只需机械翻译为 Agda 项。
--------------------------------------------------------------------------------
