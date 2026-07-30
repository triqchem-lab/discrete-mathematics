--
-- 本模块是 HFM 交叉验证测试向量, 不替代原形式化证明。
-- 主证明见: T6.agda, BurnsideT6.agda
{-# OPTIONS --rewriting #-}

-- | Sovereign.Structology.T6A4Burnside
-- T⁶/A₄ Burnside 轨道计数：A₄ 置换 T⁶ 前 4 个坐标
--
-- HFM 交叉验证 (HaskellForMaths, 见 test/T6Burnside.hs)：
--   A₄ 在 GF(3)⁴ 上的 Burnside：180/12 = 15 个轨道
--   在全 T⁶ (=GF(3)⁶) 上，后 2 坐标固定：15×9 = 135 个轨道
--
-- 不动点结构：
--   C₁ (恒等, |C|=1)：  所有 3⁴ = 81 点均不动
--   C₂ (双对换, |C|=3)：v₀=v₁, v₂=v₃ → 3² = 9 个不动点
--   C₃ (3-循环, |C|=4)：v₀=v₁=v₂, v₃ 自由 → 3² = 9 个不动点
--   C₄ (另一 3-循环, |C|=4)：同上 → 9 个不动点
--   Burnside 和 = 81 + 3·9 + 4·9 + 4·9 = 180
--   轨道数 = 180 / 12 = 15

module Sovereign.Structology.T6A4Burnside where

open import Data.Nat using (ℕ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (module ≡-Reasoning)
open ≡-Reasoning

--------------------------------------------------------------------------------
-- 1. 不动点计数
--------------------------------------------------------------------------------

-- |C₁| = 1: 恒等元固定所有 3⁴ 个 GF(3)⁴ 点
fix-identity-GF3⁴ : ℕ
fix-identity-GF3⁴ = 81  -- 3⁴

-- 对于 T⁶ (=GF(3)⁶)，仅前 4 坐标被置换，后 2 坐标固定
-- 所以全 T⁶ 上的不动点数是 GF(3)⁴ 上的 3² = 9 倍
fix-identity-T6 : ℕ
fix-identity-T6 = 729  -- 3⁶

-- |C₂| = 3: 双对换 (如 (12)(34)) 的不动点
-- 条件: v₀=v₁, v₂=v₃ → 3² = 9
fix-double-transposition-GF3⁴ : ℕ
fix-double-transposition-GF3⁴ = 9  -- 3²

-- |C₃| = |C₄| = 4: 3-循环的不动点
-- 条件: v₀=v₁=v₂, v₃ 自由 → 3² = 9
fix-3cycle-GF3⁴ : ℕ
fix-3cycle-GF3⁴ = 9  -- 3²

--------------------------------------------------------------------------------
-- 2. Burnside 公式: 轨道数 = (1/|G|) · Σ|Fix(g)|
--------------------------------------------------------------------------------

burnside-sum-GF3⁴ : ℕ
burnside-sum-GF3⁴ = 1 * fix-identity-GF3⁴
                  + 3 * fix-double-transposition-GF3⁴
                  + 4 * fix-3cycle-GF3⁴
                  + 4 * fix-3cycle-GF3⁴
  -- = 81 + 27 + 36 + 36 = 180

orbit-count-GF3⁴ : ℕ
orbit-count-GF3⁴ = 15  -- 180/12 = 15 (整除验证见 §3)

-- 在全 T⁶ (=GF(3)⁶) 上，后 2 坐标固定
-- 每个 GF(3)⁴ 轨道对应 9 个 T⁶ 轨道
orbit-count-T6 : ℕ
orbit-count-T6 = orbit-count-GF3⁴ * 9  -- 15 × 9 = 135

--------------------------------------------------------------------------------
-- 3. 验证
--------------------------------------------------------------------------------

-- Burnside 和 = 81 + 27 + 36 + 36 = 180
burnside-sum-correct : burnside-sum-GF3⁴ ≡ 180
burnside-sum-correct =
  begin
    burnside-sum-GF3⁴
  ≡⟨⟩  -- 展开
    1 * 81 + 3 * 9 + 4 * 9 + 4 * 9
  ≡⟨⟩  -- 1×81=81, 3×9=27, 4×9=36
    81 + 27 + 36 + 36
  ≡⟨⟩  -- 81+27=108
    108 + 36 + 36
  ≡⟨⟩  -- 108+36=144
    144 + 36
  ≡⟨⟩  -- 144+36=180
    180
  ∎

-- GF(3)⁴ 上轨道数 = 180/12 = 15
orbit-count-GF3⁴-correct : orbit-count-GF3⁴ ≡ 15
orbit-count-GF3⁴-correct =
  begin
    orbit-count-GF3⁴
  ≡⟨⟩  15
  ∎

-- 全 T⁶ 上轨道数 = GF(3)⁴ 轨道数 × 9 = 135
orbit-count-T6-correct : orbit-count-T6 ≡ 135
orbit-count-T6-correct =
  begin
    orbit-count-T6
  ≡⟨⟩  -- 展开: orbit-count-GF3⁴ * 9
    orbit-count-GF3⁴ * 9
  ≡⟨⟩  -- orbit-count-GF3⁴ = 15
    15 * 9
  ≡⟨⟩  -- 15×9 = 135
    135
  ∎

-- Burnside 整除验证: |A₄| × 轨道数 = Burnside 和
orbit-count-divisibility : orbit-count-GF3⁴ * 12 ≡ burnside-sum-GF3⁴
orbit-count-divisibility =
  begin
    orbit-count-GF3⁴ * 12
  ≡⟨⟩  -- 展开
    15 * 12
  ≡⟨⟩  -- 15×12 = 180
    180
  ≡⟨⟩  -- burnside-sum-GF3⁴ = 180
    burnside-sum-GF3⁴
  ∎

-- 链式一致性: T⁶ 轨道数 ≡ GF(3)⁴ 轨道数 × 9
orbit-count-chain : orbit-count-T6 ≡ orbit-count-GF3⁴ * 9
orbit-count-chain =
  begin
    orbit-count-T6
  ≡⟨⟩  orbit-count-GF3⁴ * 9
  ∎

-- 全 T⁶ 点数验证
total-points-T6 : ℕ
total-points-T6 = 729  -- 3⁶

--------------------------------------------------------------------------------
-- 4. 三重 Burnside 交叉验证 (HFM 穷举)
--
-- 同一个 729 点集上有三种不同的群作用，计算互相一致:
--
--   (a) A₄ 置换 T⁶ 前 4 坐标:
--       Burnside 和 = 1·729 + 3·81 + 4·81 + 4·81 = 1620
--       |A₄| = 12, 轨道数 = 1620/12 = 135
--
--   (b) A₄ 三维表示在 GF(3)³ (sum=0 子空间):
--       Burnside 和 = 1·27 + 3·3 + 4·3 + 4·3 = 60
--       轨道数 = 60/12 = 5
--       27 倍放大 → 5 × 27 = 135 = 轨道数(a) ✓
--
--   (c) G = C₃³ × C₂ 在 GF(9)³ 上 (BurnsideT6.agda):
--       Burnside 和 = 729 + 27 = 756
--       |G| = 54, 轨道数 = 756/54 = 14
--       1×27 + 13×54 = 729 ✓
--
--   三者全通过 HFM 穷举验证 ✅
--------------------------------------------------------------------------------

-- (a) A₄ 在完整 T⁶ 上的 Burnside
burnside-sum-T6 : ℕ
burnside-sum-T6 = 1 * 729 + 3 * 81 + 4 * 81 + 4 * 81  -- 1620

burnside-sum-T6-correct : burnside-sum-T6 ≡ 1620
burnside-sum-T6-correct =
  begin
    burnside-sum-T6
  ≡⟨⟩  1 * 729 + 3 * 81 + 4 * 81 + 4 * 81
  ≡⟨⟩  -- 1×729=729, 3×81=243, 4×81=324
    729 + 243 + 324 + 324
  ≡⟨⟩  -- 729+243=972
    972 + 324 + 324
  ≡⟨⟩  -- 972+324=1296
    1296 + 324
  ≡⟨⟩  -- 1296+324=1620
    1620
  ∎

orbit-count-T6-full : ℕ; orbit-count-T6-full = 135

orbit-count-T6-full-ok : orbit-count-T6-full ≡ 135
orbit-count-T6-full-ok =
  begin
    orbit-count-T6-full
  ≡⟨⟩  135
  ∎

-- (b) → (a) 一致性: 5 × 27 = 135
cross-check-5x27 : ℕ; cross-check-5x27 = 5 * 27  -- 135

cross-check-5x27-ok : cross-check-5x27 ≡ 135
cross-check-5x27-ok =
  begin
    cross-check-5x27
  ≡⟨⟩  5 * 27
  ≡⟨⟩  135
  ∎

-- (c) BurnsideT6 一致性
burnside-sum-G : ℕ; burnside-sum-G = 756
orbit-count-G : ℕ; orbit-count-G = 14
orbit-size-G : ℕ; orbit-size-G = 13 * 54

burnside-sum-G-ok : burnside-sum-G ≡ 756
burnside-sum-G-ok =
  begin
    burnside-sum-G
  ≡⟨⟩  729 + 27
  ≡⟨⟩  756
  ∎

orbit-count-G-ok : orbit-count-G ≡ 14
orbit-count-G-ok =
  begin
    orbit-count-G
  ≡⟨⟩  14
  ∎

orbit-size-G-ok : orbit-size-G ≡ 702
orbit-size-G-ok =
  begin
    orbit-size-G
  ≡⟨⟩  13 * 54
  ≡⟨⟩  702
  ∎
  -- 自由轨道元素数 = 13 × 54 = 702

--------------------------------------------------------------------------------
-- 5. CSP 轨道代表元分析 (CSPT6.hs 穷举)
--
-- A₄ 在 T⁶ (=GF(3)⁶) 上的 135 个轨道, 按稳定子大小分类:
--
--   |Stab|  轨道数  轨道大小  总点数   稳定子类型
--   ─────────────────────────────────────────────
--   12       27       1        27     A₄ (v₀=v₁=v₂=v₃, v₄,v₅ 自由)
--    3       54       4       216     C₃ (v₀=v₁=v₂, v₃,v₄,v₅ 自由)
--    2       27       6       162     C₂ (v₀=v₁, v₂=v₃, v₄,v₅ 自由)
--    1       27      12       324     平凡稳定子 (自由轨道)
--   ─────────────────────────────────────────────
--  合计:    135      —        729     全部匹配
--
-- HFM CSP 穷举验证 (test/CSPT6.hs):
--   canonicals: 135 reps ✅
--   orbitSizeTotal: 729 ✅
--   每类轨道数: 27/54/27/27 ✅
--------------------------------------------------------------------------------

orbit-count-stab12 : ℕ; orbit-count-stab12 = 27
orbit-size-stab12 : ℕ; orbit-size-stab12 = 1

orbit-count-stab3 : ℕ; orbit-count-stab3 = 54
orbit-size-stab3 : ℕ; orbit-size-stab3 = 4

orbit-count-stab2 : ℕ; orbit-count-stab2 = 27
orbit-size-stab2 : ℕ; orbit-size-stab2 = 6

orbit-count-stab1 : ℕ; orbit-count-stab1 = 27
orbit-size-stab1 : ℕ; orbit-size-stab1 = 12

-- 总轨道数 = 135
total-orbits-csp : ℕ
total-orbits-csp = orbit-count-stab12 + orbit-count-stab3
                 + orbit-count-stab2 + orbit-count-stab1

total-orbits-csp-ok : total-orbits-csp ≡ 135
total-orbits-csp-ok =
  begin
    total-orbits-csp
  ≡⟨⟩  27 + 54 + 27 + 27
  ≡⟨⟩  -- 27+54=81
    81 + 27 + 27
  ≡⟨⟩  -- 81+27=108
    108 + 27
  ≡⟨⟩  -- 108+27=135
    135
  ∎

-- 总点数 = 729
total-points-csp : ℕ
total-points-csp = 27 * 1 + 54 * 4 + 27 * 6 + 27 * 12

total-points-csp-ok : total-points-csp ≡ 729
total-points-csp-ok =
  begin
    total-points-csp
  ≡⟨⟩  27 * 1 + 54 * 4 + 27 * 6 + 27 * 12
  ≡⟨⟩  -- 27×1=27, 54×4=216, 27×6=162, 27×12=324
    27 + 216 + 162 + 324
  ≡⟨⟩  -- 27+216=243
    243 + 162 + 324
  ≡⟨⟩  -- 243+162=405
    405 + 324
  ≡⟨⟩  -- 405+324=729
    729
  ∎
