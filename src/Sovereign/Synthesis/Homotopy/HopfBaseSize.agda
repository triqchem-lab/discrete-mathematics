{-# OPTIONS --cubical --guardedness --rewriting #-}

-- | Sovereign.Synthesis.Homotopy.HopfBaseSize
-- 统一 T⁶ **采样点集**上三个「轨道数」的分工，终结 135 / 61 / 14 的混用
--
-- ⚠ 定位（2026-10-26 人类裁定）：本模块属于**点层（采样格点）**，不是载体层。
--   载体是**函数空间**——A₄ 上的类函数 / 表示空间，其 L² 结构由
--   `Algebra/Analytic/PlancherelTheorem.agda`（Peter-Weyl 正交基、傅里叶变换、
--   重构、列正交）与 `HilbertDiscrete.agda` 承载。
--   点层只提供**索引与采样**：`729` 是采样点数，`135/14` 是该点集在不同群下的商大小。
--   两层的数不可互推：`|A₄| = 12` 是 `dim C[A₄] = 1²+1²+1²+3²`（函数空间维数），
--   不是任一点集的势。
--
-- 同一个 T⁶（GF(3)⁶，729 点）上有三个不同的群作用，给出三个不同的底空间大小：
--
--   ① A₄（12 阶；偶置换只动前 4 坐标，后 2 坐标固定）
--        ⇒ 15 × 9 = **135** 个轨道            [T6A4Burnside.orbit-count-T6]
--   ② 涡旋群（54 阶；PolarWinding / ToroidalWinding）
--        ⇒ **14** 个轨道 = 1×27 + 13×54       [BurnsideT6.burnside-orbit-t6]
--   ③ 「~61」
--        ⇒ **不存在**。这是 HopfConstruction 头部的未验估计，
--          而 HopfConstruction 用的正是 T6.a4Action（= ①），故其底空间是 135。
--
-- 结论：三个数不是矛盾，是**三个群**。本模块把 ①② 都引用进来并证明它们互不相等，
-- 使这条分工在类型层被钉住，而不是靠注释约定。
--
-- 为什么必须分开（防止再次混用）：
--   · A₄ 的轨道大小 = 12 / |Stab| ≤ 12  ⇒ **不可能有 27 或 54 元的 A₄-轨道**；
--   · 所以「1×27 + 13×54 = 729」只能是 ② 的分解，不能写成「A₄ 轨道分解」；
--   · 反过来，②的商（14 个类）也不是 Hopf 的底空间——Hopf 的底是 ①的 135 类。
--
-- 0 postulate / 0 hole。本模块不新增数学，只把既有定理的分工形式化。

module Sovereign.Synthesis.Homotopy.HopfBaseSize where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Synthesis.A4.T6A4Burnside
  using ( orbit-count-T6; orbit-count-GF3⁴
        ; orbit-count-T6-correct; orbit-count-GF3⁴-correct )

open import Sovereign.Synthesis.Combinatorics.BurnsideT6
  using (burnside-orbit-t6; burnside-orbit-t6-value)

--------------------------------------------------------------------------------
-- ① A₄ 作用（HopfConstruction 用的那一个）⇒ 135
--------------------------------------------------------------------------------

-- HopfConstruction 的 totalProj 就是 x ↦ [x]（A₄ 轨道商），
-- 而它用的 a4Action = applyPerm (A4.perm g)，即只动前 4 坐标。
-- 故其底空间大小必须是 135，不是 61。
a4-base-size : orbit-count-T6 ≡ 135
a4-base-size = orbit-count-T6-correct

-- GF(3)⁴ 上的轨道数（Burnside：180/12）
a4-base-size-gf3⁴ : orbit-count-GF3⁴ ≡ 15
a4-base-size-gf3⁴ = orbit-count-GF3⁴-correct

--------------------------------------------------------------------------------
-- ② 涡旋群（54 阶）⇒ 14 = 1×27 + 13×54
--------------------------------------------------------------------------------

vortex-base-size : burnside-orbit-t6 ≡ 14
vortex-base-size = burnside-orbit-t6-value

--------------------------------------------------------------------------------
-- ③ 三个数互不相同：不是矛盾，是三个群
--------------------------------------------------------------------------------

-- A₄ 的商（135）≠ 涡旋群的商（14）
a4-not-vortex : ¬ (orbit-count-T6 ≡ burnside-orbit-t6)
a4-not-vortex ()

-- 61 不是 A₄ 的商
a4-not-61 : ¬ (orbit-count-T6 ≡ 61)
a4-not-61 ()

-- 61 也不是涡旋群的商
vortex-not-61 : ¬ (burnside-orbit-t6 ≡ 61)
vortex-not-61 ()
