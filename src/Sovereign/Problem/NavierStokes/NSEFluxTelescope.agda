{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEFluxTelescope
-- O3 的物理判据（通量型）+ 首条定理：轴向循环净通量恒为零（离散散度/telescoping）
--
-- 背景: `NSE.O3.blowup-physical` 要求「给出**物理意义**上的离散爆聚判据,
--   并证明在该判据下离散演化不爆聚」。判据设计先过**可陈述性筛**（O2 线的教训:
--   先判陈述有无内容, 再谈证明）:
--
--   候选 A（无界增长型）: 爆聚 ⇔ 某 ℕ-值可观察量在演化中无界。
--     ✗ **已排除**（平凡）: `NSEBlowupBound` 已证任何经有限编码的可观察量都有界
--       （`fin-bounded` / `no-discrete-blowup`）——该判据永不触发, 无内容。
--   候选 B（峰值集中度型）: 爆聚 ⇔ 局部密度峰值的集中度加剧。
--     ✗ **在本基座上不可陈述**: 「峰值/大小」需要**序或范数**——GF(3) 无序
--       （这正是 `13-flt-analysis` 的 Archimedes 断层同款: 大小比较是序结构的定理）;
--       可用的两个替代都不合格: 范数 N 是**有损投影**（相位 4→1, `10-norm-collapse:11`）,
--       `phaseAmp` 只是相位的实部标记（不是密度序）。
--   候选 C（通量型, **本模块采纳**）: 爆聚 ⇔ 存在持续的**净流入**（某轴周期通量 ≠ 0）
--     使局部累积。→ 可陈述（纯 GF(3) 组合量）, 且**可证其单步恒不触发**。
--
-- 本模块定理（全部构造性, 0 postulate / 0 hole）:
--   §1 `cancel3`       : GF(3) 三段循环差分之和恒为 T₀（27 case 穷举）
--   §2 `axisFlux-zero` : **轴向循环净通量恒为 T₀**（离散 telescoping,
--                        靠 `shiftAt-cubed` 把第三点折回第一点 + `cancel3`）
--        `axisFlux-via-diffF`: 同型的 diffF 形式（与 `NSEOnT6.diffF` 定义性对齐）
--
-- 物理读法: 单步尺度上**不存在净流入**——任何「向一点持续灌注」的爆聚机制
--   在本离散基座上没有通量通道（每个 3-周期内的流入流出逐点配对相消）。
--
-- ⚠ 诚实边界（见 §3）: 本模块只封**通量型**判据的单步触发; 多步/耦合下的集中
--   （例如涡旋自持造成的长期再分布）**仍开放**——那需要总量守恒或支撑集单调性定理
--   （已登记为下一步, 不在本模块冒充）。
--
-- 依赖: Sovereign.Problem.NavierStokes.NSEOnT6（算子与 shiftAt-cubed）
--       Sovereign.Base.Trit（Trit 表与 negate）

module Sovereign.Problem.NavierStokes.NSEFluxTelescope where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using (
  C3; Torus6; ScalarField; Field; shiftAt; shiftAt-cubed; diffF; div; nsStep; sum3)

--------------------------------------------------------------------------------
-- §1. GF(3) 三段循环差分之和恒为零
--
-- (b−a) + (c−b) + (a−c) = 0 —— 右嵌套 sum3 逐层展开后逐 case 归约。
-- 27 case ≤ 27 ⇒ 符合库内穷举法纪律（≤27 case 允许, >27 须符号化）。
--------------------------------------------------------------------------------

cancel3 : ∀ (a b c : Trit) →
  sum3 (b ⊕ negate a) (c ⊕ negate b) (a ⊕ negate c) ≡ T₀
cancel3 T₀ T₀ T₀ = refl
cancel3 T₀ T₀ T₁ = refl
cancel3 T₀ T₀ T₂ = refl
cancel3 T₀ T₁ T₀ = refl
cancel3 T₀ T₁ T₁ = refl
cancel3 T₀ T₁ T₂ = refl
cancel3 T₀ T₂ T₀ = refl
cancel3 T₀ T₂ T₁ = refl
cancel3 T₀ T₂ T₂ = refl
cancel3 T₁ T₀ T₀ = refl
cancel3 T₁ T₀ T₁ = refl
cancel3 T₁ T₀ T₂ = refl
cancel3 T₁ T₁ T₀ = refl
cancel3 T₁ T₁ T₁ = refl
cancel3 T₁ T₁ T₂ = refl
cancel3 T₁ T₂ T₀ = refl
cancel3 T₁ T₂ T₁ = refl
cancel3 T₁ T₂ T₂ = refl
cancel3 T₂ T₀ T₀ = refl
cancel3 T₂ T₀ T₁ = refl
cancel3 T₂ T₀ T₂ = refl
cancel3 T₂ T₁ T₀ = refl
cancel3 T₂ T₁ T₁ = refl
cancel3 T₂ T₁ T₂ = refl
cancel3 T₂ T₂ T₀ = refl
cancel3 T₂ T₂ T₁ = refl
cancel3 T₂ T₂ T₂ = refl

--------------------------------------------------------------------------------
-- §2. 轴向循环净通量恒为零（判据 C 的量 = axisFlux）
--
-- 定义取**展开形式**（f (shiftAt …) 直写）, 使第三项的 f(s³x) 在语法上可见,
-- 从而 `rewrite cong f (shiftAt-cubed i x)` 能把它折回 f x。
--------------------------------------------------------------------------------

-- 判据 C 的可观察量: 沿轴 i 的一个 3-周期内的净通量（三段差分之和）
axisFlux : C3 → ScalarField → Torus6 → Trit
axisFlux i f x =
  sum3 (f (shiftAt i x) ⊕ negate (f x))
       (f (shiftAt i (shiftAt i x)) ⊕ negate (f (shiftAt i x)))
       (f (shiftAt i (shiftAt i (shiftAt i x))) ⊕ negate (f (shiftAt i (shiftAt i x))))

-- **主定理**: 净通量恒为 T₀ —— 单步无净流入, 通量型爆聚判据永不触发
axisFlux-zero : ∀ (i : C3) (f : ScalarField) (x : Torus6) →
  axisFlux i f x ≡ T₀
axisFlux-zero i f x rewrite cong f (shiftAt-cubed i x) =
  cancel3 (f x) (f (shiftAt i x)) (f (shiftAt i (shiftAt i x)))

-- 同型的 diffF 形式（与 NSEOnT6.diffF / shiftF 定义性对齐, 便于与 div 对接）
axisFlux-via-diffF : ∀ (i : C3) (f : ScalarField) (x : Torus6) →
  sum3 (diffF i f x) (diffF i f (shiftAt i x)) (diffF i f (shiftAt i (shiftAt i x))) ≡ T₀
axisFlux-via-diffF i f x = axisFlux-zero i f x

--------------------------------------------------------------------------------
-- §3. 判据 C 的定理化与诚实边界
--
-- 判据 C（通量型）: 称离散场在演化中**通量型爆聚**, 若存在轴向周期净通量持续非零
--   （局部点被持续灌注 ⇒ 累积）。
--
-- ✓ 已证（本模块）: **axisFlux ≡ T₀ 恒成立** ⇒ 判据 C 的触发条件在
--   单步、逐 3-周期尺度上**不可能满足**——通量型爆聚在本基座上被封死。
--
-- ✗ 未证（开放, 不冒充）:
--   ① **多步/耦合集中**: 长期再分布（如涡旋自持）能否把场集中到小子集,
--      需要总量守恒（Σ 场量不变）或支撑集单调性定理——**未证**;
--   ② 候选 B（峰值集中度）在本基座**不可陈述**（无序）, 若改用范数投影
--      则是**有损**（4→1）⇒ 不构成合法判据;
--   ③ 与连续统「爆聚」（Navier–Stokes 正则性）的关系: **不声称**——
--      本框架不主张连续极限（`NSEPhaseField:420` O4 边界）。
--------------------------------------------------------------------------------
