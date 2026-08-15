{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.RandomMatrixMoments
-- 62 统计学 (62-05/06/07 诚实版) — 对称矩阵系综的精确迹矩 (0 postulate)
--
-- 对"离散 Catalan 定理"的**计算验证后判定** (验证脚本: 全枚举):
--   ✓ 奇矩精确为零 (平衡二值系综 {±1} 中心化)
--   ✓ μ₂ 精确 = C₁·σ² = 1 (N=2,3)
--   ✗ μ₂ₖ = Cₖ 精确 (N ≥ 2k) — **不成立**: 有限 N 交叉配对修正不消失:
--       N=2: μ₄ = 3/2 = C₂ − 1/2;  N=3: μ₄ = 5/3 = C₂ − 1/3
--   成立的是"极限 Catalan + 1/N 修正" — 本模块如实形式化修正结构,
--   不以断言代替计算 (宪法: 先算后写)。

module Sovereign.Analysis.RandomMatrixMoments where

open import Data.Nat using (ℕ; _*_; _+_; _∸_)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- 局部 ℤ 算子
_⊞_ : ℤ → ℤ → ℤ ; _⊞_ = Data.Integer._+_
_⊠_ : ℤ → ℤ → ℤ ; _⊠_ = Data.Integer._*_
infixl 20 _⊞_ ; infixl 25 _⊠_

--------------------------------------------------------------------------------
-- §1. N=2 对称矩阵 {±1} 系综: 迹的公式与 8 行表
--------------------------------------------------------------------------------

-- M = [[a, c], [c, b]] 的迹 (嵌套矩阵幂, ℤ 字面归约)
tr1 : ℤ → ℤ → ℤ → ℤ
tr1 a b c = a ⊞ b

tr2 : ℤ → ℤ → ℤ → ℤ
tr2 a b c = (a ⊠ a ⊞ c ⊠ c) ⊞ (b ⊠ b ⊞ c ⊠ c)

tr3 : ℤ → ℤ → ℤ → ℤ
tr3 a b c =
  let m2-00 = a ⊠ a ⊞ c ⊠ c
      m2-01 = c ⊠ (a ⊞ b)
      m2-11 = b ⊠ b ⊞ c ⊠ c
  in (m2-00 ⊠ a ⊞ m2-01 ⊠ c) ⊞ (m2-01 ⊠ c ⊞ m2-11 ⊠ b)

tr4 : ℤ → ℤ → ℤ → ℤ
tr4 a b c =
  let m2-00 = a ⊠ a ⊞ c ⊠ c
      m2-01 = c ⊠ (a ⊞ b)
      m2-11 = b ⊠ b ⊞ c ⊠ c
  in (m2-00 ⊠ m2-00 ⊞ m2-01 ⊠ m2-01) ⊞ (m2-01 ⊠ m2-01 ⊞ m2-11 ⊠ m2-11)

m1 = -[1+ 0 ]  -- −1
p1 = + 1        -- +1

-- 8 行表 (每行 4 迹)
row-mmm-1 : tr1 m1 m1 m1 ≡ -[1+ 1 ] ; row-mmm-1 = refl
row-mmm-2 : tr2 m1 m1 m1 ≡ + 4       ; row-mmm-2 = refl
row-mmm-3 : tr3 m1 m1 m1 ≡ -[1+ 7 ]  ; row-mmm-3 = refl
row-mmm-4 : tr4 m1 m1 m1 ≡ + 16      ; row-mmm-4 = refl
row-mmp-1 : tr1 m1 m1 p1 ≡ -[1+ 1 ]  ; row-mmp-1 = refl
row-mmp-2 : tr2 m1 m1 p1 ≡ + 4       ; row-mmp-2 = refl
row-mmp-3 : tr3 m1 m1 p1 ≡ -[1+ 7 ]  ; row-mmp-3 = refl
row-mmp-4 : tr4 m1 m1 p1 ≡ + 16      ; row-mmp-4 = refl
row-mpm-1 : tr1 m1 p1 m1 ≡ + 0       ; row-mpm-1 = refl
row-mpm-2 : tr2 m1 p1 m1 ≡ + 4       ; row-mpm-2 = refl
row-mpm-3 : tr3 m1 p1 m1 ≡ + 0       ; row-mpm-3 = refl
row-mpm-4 : tr4 m1 p1 m1 ≡ + 8       ; row-mpm-4 = refl
row-mpp-1 : tr1 m1 p1 p1 ≡ + 0       ; row-mpp-1 = refl
row-mpp-2 : tr2 m1 p1 p1 ≡ + 4       ; row-mpp-2 = refl
row-mpp-3 : tr3 m1 p1 p1 ≡ + 0       ; row-mpp-3 = refl
row-mpp-4 : tr4 m1 p1 p1 ≡ + 8       ; row-mpp-4 = refl
row-pmm-1 : tr1 p1 m1 m1 ≡ + 0       ; row-pmm-1 = refl
row-pmm-2 : tr2 p1 m1 m1 ≡ + 4       ; row-pmm-2 = refl
row-pmm-3 : tr3 p1 m1 m1 ≡ + 0       ; row-pmm-3 = refl
row-pmm-4 : tr4 p1 m1 m1 ≡ + 8       ; row-pmm-4 = refl
row-pmp-1 : tr1 p1 m1 p1 ≡ + 0       ; row-pmp-1 = refl
row-pmp-2 : tr2 p1 m1 p1 ≡ + 4       ; row-pmp-2 = refl
row-pmp-3 : tr3 p1 m1 p1 ≡ + 0       ; row-pmp-3 = refl
row-pmp-4 : tr4 p1 m1 p1 ≡ + 8       ; row-pmp-4 = refl
row-ppm-1 : tr1 p1 p1 m1 ≡ + 2       ; row-ppm-1 = refl
row-ppm-2 : tr2 p1 p1 m1 ≡ + 4       ; row-ppm-2 = refl
row-ppm-3 : tr3 p1 p1 m1 ≡ + 8       ; row-ppm-3 = refl
row-ppm-4 : tr4 p1 p1 m1 ≡ + 16      ; row-ppm-4 = refl
row-ppp-1 : tr1 p1 p1 p1 ≡ + 2       ; row-ppp-1 = refl
row-ppp-2 : tr2 p1 p1 p1 ≡ + 4       ; row-ppp-2 = refl
row-ppp-3 : tr3 p1 p1 p1 ≡ + 8       ; row-ppp-3 = refl
row-ppp-4 : tr4 p1 p1 p1 ≡ + 16      ; row-ppp-4 = refl

--------------------------------------------------------------------------------
-- §2. N=2 矩: 奇矩为零, μ₂ 精确 Catalan, μ₄ 带 1/N 修正
--------------------------------------------------------------------------------

-- 8 项和 (奇矩精确为零)
sum-tr1 : ((((((tr1 m1 m1 m1 ⊞ tr1 m1 m1 p1) ⊞ tr1 m1 p1 m1) ⊞ tr1 m1 p1 p1)
          ⊞ tr1 p1 m1 m1) ⊞ tr1 p1 m1 p1) ⊞ tr1 p1 p1 m1) ⊞ tr1 p1 p1 p1 ≡ + 0
sum-tr1 = refl

sum-tr3 : ((((((tr3 m1 m1 m1 ⊞ tr3 m1 m1 p1) ⊞ tr3 m1 p1 m1) ⊞ tr3 m1 p1 p1)
          ⊞ tr3 p1 m1 m1) ⊞ tr3 p1 m1 p1) ⊞ tr3 p1 p1 m1) ⊞ tr3 p1 p1 p1 ≡ + 0
sum-tr3 = refl

-- μ₂ = 1 精确: Σ tr² = 32 = 8·1·2² (C₁·σ² 精确, 每矩阵 tr² = 4 常数)
sum-tr2 : ((((((tr2 m1 m1 m1 ⊞ tr2 m1 m1 p1) ⊞ tr2 m1 p1 m1) ⊞ tr2 m1 p1 p1)
          ⊞ tr2 p1 m1 m1) ⊞ tr2 p1 m1 p1) ⊞ tr2 p1 p1 m1) ⊞ tr2 p1 p1 p1 ≡ + 32
sum-tr2 = refl

moment-2-exact-catalan : 32 ≡ 8 * 1 * 2 * 2
moment-2-exact-catalan = refl

-- μ₄ = 3/2 = C₂ − 1/2: Σ tr⁴ = 96 = 8·(2·2³ − 4·2·... ) —
--   整数陈述: 96 = 8·2·2³ − 8·4·2·1 = 128 − 32
sum-tr4 : ((((((tr4 m1 m1 m1 ⊞ tr4 m1 m1 p1) ⊞ tr4 m1 p1 m1) ⊞ tr4 m1 p1 p1)
          ⊞ tr4 p1 m1 m1) ⊞ tr4 p1 m1 p1) ⊞ tr4 p1 p1 m1) ⊞ tr4 p1 p1 p1 ≡ + 96
sum-tr4 = refl

moment-4-correction : 96 ≡ 8 * 2 * 2 * 2 * 2 ∸ 8 * 4
moment-4-correction = refl
--   128 = 8·C₂·N³ (Catalan 预测), 32 = 8·N (交叉配对修正) — 1/N 修正结构

--------------------------------------------------------------------------------
-- §3. N=3: μ₂ 常数 9 精确, μ₄ 的 64 项和与修正
--------------------------------------------------------------------------------

-- tr(M²) = Σᵢ Mᵢᵢ² + 2·Σ_{i<j} Mᵢⱼ² = 9 常数 (±1 平方 = 1)
-- 故 Σ tr² = 64·9 = 576
moment-2-n3-exact : 64 * 9 ≡ 576
moment-2-n3-exact = refl

-- Σ tr⁴ = 2880 = 64·(2·27) − 64·9 = 64·45 — μ₄ = 5/3 = C₂ − 1/3
sum-tr4-n3 :
      (+ 81) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 81)
    ⊞ (+ 33) ⊞ (+ 81) ⊞ (+ 81) ⊞ (+ 33)
    ⊞ (+ 49) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 49)
    ⊞ (+ 33) ⊞ (+ 49) ⊞ (+ 49) ⊞ (+ 33)
    ⊞ (+ 49) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 49)
    ⊞ (+ 33) ⊞ (+ 49) ⊞ (+ 49) ⊞ (+ 33)
    ⊞ (+ 33) ⊞ (+ 49) ⊞ (+ 49) ⊞ (+ 33)
    ⊞ (+ 49) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 49)
    ⊞ (+ 49) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 49)
    ⊞ (+ 33) ⊞ (+ 49) ⊞ (+ 49) ⊞ (+ 33)
    ⊞ (+ 33) ⊞ (+ 49) ⊞ (+ 49) ⊞ (+ 33)
    ⊞ (+ 49) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 49)
    ⊞ (+ 33) ⊞ (+ 49) ⊞ (+ 49) ⊞ (+ 33)
    ⊞ (+ 49) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 49)
    ⊞ (+ 33) ⊞ (+ 81) ⊞ (+ 81) ⊞ (+ 33)
    ⊞ (+ 81) ⊞ (+ 33) ⊞ (+ 33) ⊞ (+ 81) ≡ + 2880
sum-tr4-n3 = refl

moment-4-n3-correction : 2880 ≡ 64 * 54 ∸ 64 * 9
moment-4-n3-correction = refl
--   64·54 = 64·C₂·N³ (Catalan 预测 3456), 64·9 = 64·N (修正) — 1/N 结构一致

--------------------------------------------------------------------------------
-- §4. 诚实结论 (验证脚本判定, 落库):
--   "离散 Catalan 定理 (N ≥ 2k 精确)" **不成立** —
--   精确成立的是: 奇矩 = 0, μ₂ = C₁·σ², μ₄ = C₂ − 1/N (N=2,3 两见证);
--   极限注释: μ₄ → C₂ (N → ∞) 由修正项 1/N 承载, 不进入证明层。
--------------------------------------------------------------------------------

-- 0 postulate.
