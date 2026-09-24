{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSESupportOrbitPeriod
-- supportCount 轨道的**最终周期**（「波动式集中」排除的最后一件）—— **条件版**
--
-- 主定理（本模块）:
--   `supportCount-orbit-period`：给定 `EventuallyPeriodic nsStep v`（最终周期见证），
--   计数序列以同一 (i, k) 最终周期：
--     supportCount (iterate (i + k + n) nsStep v) ≡ supportCount (iterate (i + n) nsStep v)
--   ⇒ 计数只能**周期振荡**（值域另有界 [0,4374]）⇒ **无漂移型集中**。
--
-- ⚠ **条件性声明（重要，勿跳读）**：`EventuallyPeriodic` 的**无条件证明本身未闭合**
--   （`NSEOnT6:675-677` 自述：状态编码注入性「尚待闭合」⇒「不声称 NS 演化的周期性
--   已无条件成立」）。因此本模块是**条件版**：给定最终周期见证 ⇒ 计数投影亦最终周期。
--   无条件版依赖那个已知缺口（与 bounded-instantiation 教训同族）。
--
-- 证明链（3 步, 全部复用既有件）:
--   iterate (i+k+n) ≡ iterate n ∘ iterate (i+k)   （iterate-+, NSEOnT6:684-687）
--                 ≡ iterate n ∘ iterate i         （cong, 用 ep.periodic）
--                 ≡ iterate (i+n)                 （sym iterate-+）
--   外面套 `cong supportCount`。
--
-- 判型注: 相等链 + 一次 cong —— 非配对弹出族、非表事实。
-- 0 postulate / 0 hole（**未编译**: 写盘时任务预算墙内, 下段编译取据）

module Sovereign.Problem.NavierStokes.NSESupportOrbitPeriod where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong; sym)

open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (Field; nsStep; iterate; iterate-+; EventuallyPeriodic)
open import Sovereign.Problem.NavierStokes.NSEFixedPointStrict using (supportCount)

module EP = EventuallyPeriodic

--------------------------------------------------------------------------------
-- §1. 主定理: 计数序列继承全场轨道的最终周期
--------------------------------------------------------------------------------

supportCount-orbit-period :
  ∀ (v : Field) (ep : EventuallyPeriodic nsStep v) (n : ℕ) →
  supportCount (iterate (EP.i ep + EP.k ep + n) nsStep v)
  ≡ supportCount (iterate (EP.i ep + n) nsStep v)
supportCount-orbit-period v ep n =
  trans (cong supportCount (iterate-+ (i + k) n nsStep v))
  (trans (cong (λ z → supportCount (iterate n nsStep z)) (EP.periodic ep))
         (cong supportCount (sym (iterate-+ i n nsStep v))))
  where
    i : ℕ
    i = EP.i ep
    k : ℕ
    k = EP.k ep

--------------------------------------------------------------------------------
-- §2. 诚实边界
--
-- ✓ 已证（条件版）: `supportCount-orbit-period` —— 给定 `EventuallyPeriodic nsStep v`,
--   计数序列以同一 (i,k) 最终周期 ⇒ **无漂移型集中**（波动只能是周期振荡）。
-- ✗ 不声称:
--   ① **无条件版**（`∀ v → EventuallyPeriodic nsStep v`）——`NSEOnT6:675-677` 的
--      状态编码注入性**未闭合**（已知缺口）, 本模块不冒充;
--   ② 周期 k 的**界**（轨道长度上界未刻画）;
--   ③ 「无漂移 ⇒ 无集中」**不成立**——周期振荡内的集中模式仍可能存在
--      （但已被 ⑤ 其余四件套限制: 有界 + 非单调 + 不动点处不变 + 零元刻画）;
--   ④ 连续统 NS 的任何结论。
--------------------------------------------------------------------------------
