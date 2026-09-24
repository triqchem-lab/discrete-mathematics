{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEIterate
-- n 步不变量保持: 总量与不可压性在 `iterate n nsStep` 下保持
--
-- 背景: 前两批封了 `nsStep` **单步**的两条集中通道:
--   · 总量增减 → `NSEConservation.total-nsStep`（总量不变）
--   · 压缩聚集 → `NSEIncompressible.nsStep-incompressible`（不可压保持）
-- 本模块把它们升到 **n 步**（O3「多步/耦合集中」问题的不变量部分）。
--
-- 结构（0 postulate / 0 hole）:
--   §1 `iterate-total`         : ∀ n v → totalF (iterate n nsStep v) ≡ totalF v
--   §2 `iterate-incompressible`: ∀ n v → Incompressible v → Incompressible (iterate n nsStep v)
--   §3 对抗验证（n = 0/1 的 refl 级核对）与诚实边界
--
-- 合成陈述（跨模块, 只记不证——各分量均有回执/命令级证据）:
--   轨道在本离散基座上**不会跑飞**: 有界（NSEBlowupBound: 可观察量全有界）
--   + 总量恒定（本模块 §1）+ 不可压保持（§2）+ 最终周期（NSE.T13 通用引理）。
--   ⚠ 但**仍不等于**「无集中」——再分布/集中度仍开放（支撑集定理未做）。
--
-- ⚠ 迭代方向（与库内定义对齐）: `iterate (suc n) f x = iterate n f (f x)`
--   （NSEOnT6:681-682）—— 即先作用 f 再递归, 归纳步的归纳假设在 `f x` 处取用。
--
-- 依赖: NSEConservation（totalF/total-nsStep）, NSEIncompressible（nsStep-incompressible）,
--       NSEOnT6（Field/Incompressible/nsStep/iterate）

module Sovereign.Problem.NavierStokes.NSEIterate where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (Field; Incompressible; nsStep; iterate)
open import Sovereign.Problem.NavierStokes.NSEConservation using (totalF; total-nsStep)
open import Sovereign.Problem.NavierStokes.NSEIncompressible using (nsStep-incompressible)

--------------------------------------------------------------------------------
-- §1. n 步总量不变
--------------------------------------------------------------------------------

iterate-total : ∀ (n : ℕ) (v : Field) →
  totalF (iterate n nsStep v) ≡ totalF v
iterate-total zero v = refl
iterate-total (suc n) v =
  trans (iterate-total n (nsStep v)) (total-nsStep v)

--------------------------------------------------------------------------------
-- §2. n 步不可压保持
--------------------------------------------------------------------------------

iterate-incompressible : ∀ (n : ℕ) (v : Field) →
  Incompressible v → Incompressible (iterate n nsStep v)
iterate-incompressible zero v inc = inc
iterate-incompressible (suc n) v inc =
  iterate-incompressible n (nsStep v) (nsStep-incompressible v inc)

--------------------------------------------------------------------------------
-- §3. 对抗验证与诚实边界
--
-- 对抗验证（纪律 §6）: n = 0 与 n = 1 的实例与单步定理**定义性一致**
-- （iterate zero f x ≡ x; iterate one f x ≡ f x）, 故两条定理在边界上
-- 退化为上两批的单步结果——不存在「n 步版本与单步版本不兼容」的缝。
--
-- ✓ 已证: §1 / §2（构造性归纳, 无 postulate）。
-- ✗ 不声称:
--   ① 「无集中」——本模块只保**不变量**; 再分布/集中度（支撑集定理）仍开放;
--   ② 连续统 NS 的任何结论（不主张连续极限）;
--   ③ 最终周期性的具体周期（那是 NSE.T13 通用引理的内容, 本模块不重复）。
--------------------------------------------------------------------------------
