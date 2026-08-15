{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.GoodnessOfFitGF3
-- 62-20 拟合优度检验 — 幻方识别的 χ² 零检验 (0 postulate)
--
-- 骨架中的 ℚ 除法与序改用 ℕ 分子形式 (更诚实, 无实数分析):
--   χ² = Σ (Oᵢ−Eᵢ)²/Eᵢ, Eᵢ = 15 恒定 — 零检验 ⟺ 分子 Σ (Oᵢ−15)² = 0
-- 本模块只写可证的实例部分 (按"先算后写"纪律):
--   §1 Lo Shu 3×3 幻方: 8 线 (3 行+3 列+2 对角) 全 ≡ 15
--   §2 幻方零检验: chi2-num ≡ 0 (refl)
--   §3 非幻方正检验: 单线偏离 14 → chi2-num ≡ 1 ≢ 0
--   §4 小规模精确分布与 4×4/12×12 对接: 注释级 (数据提取留待, 不占位)

module Sovereign.Analysis.GoodnessOfFitGF3 where

open import Data.Nat using (ℕ; _+_; _*_; _∸_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- §1. Lo Shu 3×3 幻方: 8 线全 ≡ 15
--------------------------------------------------------------------------------

-- Lo Shu: [[8,1,6],[3,5,7],[4,9,2]] — 3 行
loshu-row-1 : 8 + 1 + 6 ≡ 15 ; loshu-row-1 = refl
loshu-row-2 : 3 + 5 + 7 ≡ 15 ; loshu-row-2 = refl
loshu-row-3 : 4 + 9 + 2 ≡ 15 ; loshu-row-3 = refl

-- 3 列
loshu-col-1 : 8 + 3 + 4 ≡ 15 ; loshu-col-1 = refl
loshu-col-2 : 1 + 5 + 9 ≡ 15 ; loshu-col-2 = refl
loshu-col-3 : 6 + 7 + 2 ≡ 15 ; loshu-col-3 = refl

-- 2 对角
loshu-diag-1 : 8 + 5 + 2 ≡ 15 ; loshu-diag-1 = refl
loshu-diag-2 : 6 + 5 + 4 ≡ 15 ; loshu-diag-2 = refl

--------------------------------------------------------------------------------
-- §2. χ² 分子统计量 (E = 15 恒定, 分母并入 — 零检验等价)
--------------------------------------------------------------------------------

-- 偏差 |l − 15| (ℕ 饱和减法的双侧差 — 14 与 16 的偏差均 = 1)
dev : ℕ → ℕ
dev l = (15 ∸ l) + (l ∸ 15)

-- chi2-num = Σ_{8 线} dev(Oᵢ)² — 各线观测值的 8 元函数
chi2-num : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
chi2-num l1 l2 l3 l4 l5 l6 l7 l8 =
  (dev l1 * dev l1) + (dev l2 * dev l2)
  + (dev l3 * dev l3) + (dev l4 * dev l4)
  + (dev l5 * dev l5) + (dev l6 * dev l6)
  + (dev l7 * dev l7) + (dev l8 * dev l8)

-- 幻方零检验: 8 线全 15 → chi2-num ≡ 0
magic-square-chi2-zero : chi2-num 15 15 15 15 15 15 15 15 ≡ 0
magic-square-chi2-zero = refl

-- Lo Shu 的检验实例 (8 线值代入)
loshu-chi2-zero : chi2-num 15 15 15 15 15 15 15 15 ≡ 0
loshu-chi2-zero = refl

--------------------------------------------------------------------------------
-- §3. 非幻方正检验: 单线偏离 → chi2-num > 0
--------------------------------------------------------------------------------

-- 一行和为 14 (偏离理想 15): (14−15)² = 1 → chi2-num ≡ 1
nonmagic-chi2-positive-num : chi2-num 14 15 15 15 15 15 15 15 ≡ 1
nonmagic-chi2-positive-num = refl

-- 正性 (ℕ: 1 ≢ 0 — 非幻方被判别)
nonmagic-detected : ¬ (chi2-num 14 15 15 15 15 15 15 15 ≡ 0)
nonmagic-detected ()

-- 两线偏离: (14−15)² + (16−15)² = 1 + 1 = 2
nonmagic-two-lines : chi2-num 14 16 15 15 15 15 15 15 ≡ 2
nonmagic-two-lines = refl

--------------------------------------------------------------------------------
-- §4. 判别语义 (注释级, 按"先算后写"纪律):
--   幻方 ⟹ χ² = 0 (§2 已证实例); 非幻方 ⟹ χ² > 0 (§3 已证实例) —
--   判别器语义: chi2-num ≡ 0 当且仅当 8 线全 = 15。
--   全称版 (任意 8 线向量的 ⟺) 需 ℕ 平方和引理; 4×4 (MagicSquareM4)
--   与 12×12 (MagicSquare144) 的对接需行/列/对角数据提取函数 —
--   均如实留待, 不以 postulate 或洞占位。
--------------------------------------------------------------------------------

-- 0 postulate.
