{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEMadelungRefuted
-- (★) 平方恒等式的**反例** —— 受约束版 Madelung 耦合为假（构造性见证）
--
-- 背景: O2 线的三度收束。
--   ① `NSEMadelungNonTrivial`: 原 O2（∀-字段有无实例）**恒真、无内容**（record 欠约束）；
--   ② `NSEMadelungConstrained`: 「钉死 Qphase」的重述**仍然空洞**（transport 仍自由），
--      并归约出真正的尖锐形态
--        (★)  ∀ θ x → (phaseDiff zero θ x)² ≡ quantumPotentialPhase θ x
--      （`coupling⇒square` / `square⇒coupling` 双向等价）；
--   ③ **本模块**: 给出 (★) 的**反例** ⇒ 受约束版耦合方程**为假**。
--
-- 反例（全部由 refl 归约确认, 见 §2）:
--   θ = theta-e1（`NSEPhaseField:443`, 单点凸起 a1 于 e₁ = (1,0,0,0,0,0)）
--   x = x₁₂   = (1,2,0,0,0,0)
--   逐轴相位输运（shiftAt 循环 0→1→2→0, NSEPhaseField:67-80）:
--     Π₀ = θ(x+e₁)·θ(x)⁻¹ = θ(2,2,0,0,0,0)·a0 = a0
--     Π₁ = θ(x+e₂)·θ(x)⁻¹ = θ(1,0,0,0,0,0)·a0 = a1   ← 唯一非平凡
--     Π₂ = θ(x+e₃)·θ(x)⁻¹ = θ(1,2,1,0,0,0)·a0 = a0
--   左端 = Π₀² = a0;
--   右端 = phaseConjugate(Π₀Π₁Π₂Π₀Π₁Π₂) = phaseConjugate(a1·a1) = phaseConjugate(a2) = a2
--          （σ 的核 = {a0,a2}, 故 σ(a2) = a2）。
--   ⇒ a0 ≢ a2, (★) 崩。
--
-- ⚠ 语义定位: 这**不是**对新闻证明的反驳（那证明在 ℕ/F_p 上, 与本模块不同基座）,
--   而是**我们自己归约出的义务的闭合**——闭合方式是「反例击穿」, 符合库内既定原则
--   （`19-review-list`: 真命题可证, **假命题裁剪**）。
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEMadelungRefuted where

open import Data.Product using (Σ; _,_)
open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Sovereign.Algebra.GroupTheory.DuodecClock using (AlphaPower; a0; a1; a2; mulAlpha)
open import Sovereign.Problem.NavierStokes.NSEPhaseField using (
  Torus6; PhField; phaseDiff; pressurePhase; quantumPotentialPhase; theta-e1)
open import Sovereign.Problem.NavierStokes.NSEMadelungConstrained using (coupling⇒square)

--------------------------------------------------------------------------------
-- §1. 反例点
--------------------------------------------------------------------------------

x₁₂ : Torus6
x₁₂ = suc zero , suc (suc zero) , zero , zero , zero , zero

--------------------------------------------------------------------------------
-- §2. 三条 refl 交叉核对（对抗验证协议 §6：具体点独立比对）
--------------------------------------------------------------------------------

phaseDiff-zero-at : phaseDiff zero theta-e1 x₁₂ ≡ a0
phaseDiff-zero-at = refl

phaseDiff-one-at : phaseDiff (suc zero) theta-e1 x₁₂ ≡ a1
phaseDiff-one-at = refl

qphase-at : quantumPotentialPhase theta-e1 x₁₂ ≡ a2
qphase-at = refl

--------------------------------------------------------------------------------
-- §3. (★) 在 (theta-e1, x₁₂) 处崩掉：a0 ≢ a2
--------------------------------------------------------------------------------

star-fails :
  mulAlpha (phaseDiff zero theta-e1 x₁₂) (phaseDiff zero theta-e1 x₁₂)
  ≢ quantumPotentialPhase theta-e1 x₁₂
star-fails ()

-- 全称版 (★) 的否定（Σ 见证形式）
star-refuted : Σ PhField (λ θ → Σ Torus6 (λ x →
  mulAlpha (phaseDiff zero θ x) (phaseDiff zero θ x)
  ≢ quantumPotentialPhase θ x))
star-refuted = theta-e1 , x₁₂ , star-fails

--------------------------------------------------------------------------------
-- §4. 推论: 受约束版 Madelung 耦合方程（两边都由场决定）为假
--
-- 由 `NSEMadelungConstrained.coupling⇒square`: p ≡ Q·p⁻¹ ⇒ p² ≡ Q。
-- 反例点上 p² = a0 ≠ a2 = Q ⇒ 该耦合方程在 (theta-e1, x₁₂) 不成立。
--------------------------------------------------------------------------------

coupling-full-refuted : Σ PhField (λ θ → Σ Torus6 (λ x →
  phaseDiff zero θ x
  ≢ mulAlpha (quantumPotentialPhase θ x) (pressurePhase θ x)))
coupling-full-refuted =
  theta-e1 , x₁₂ , (λ eq → star-fails (coupling⇒square _ _ eq))

--------------------------------------------------------------------------------
-- §5. 诚实边界
--
-- ✓ 已证（本模块, 构造性）: (★) 为假（反例 θ = theta-e1, x = x₁₂）;
--   受约束版耦合方程为假（同一见证, 经 coupling⇒square）。
-- ✗ 不声称:
--   ① 这**不**反驳外部（ℕ/F_p 基座上的）任何定理——不同基座、不同定义域;
--   ② O2 线的**物理判据**（`NSE.O3.blowup-physical` 一族的「物理爆聚」）仍开放;
--   ③ 若重新设计 Qphase/pressurePhase 的**形式**（例如引入幅度层）, 新方程可能为真
--      —— 本模块只裁定**当前形式**为假。
--------------------------------------------------------------------------------
