{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEMadelungNonTrivial
-- Madelung 耦合的 ∀-版 (NSEPhaseField 的 O2)：给出实例 + 判定该陈述是否有意义
--
-- 背景 (NSEPhaseField.agda:366-370 原文):
--   「O2 (待证): 是否存在非平凡的 θ 使 coupling 成立?
--     —— 若 Qphase 与 pressurePhase 的定义使 RHS 恒为 a0, 则方程退化为「无转动」。
--        需要重新设计 Qphase 使之非平凡。这是本模块最关键的开放点。」
--   而 §4d (:471-474) 自陈: 「这只是**单点**等式, 不是 ∀-律。
--     故 MadelungCoupling 的 ∀-字段仍**无实例**。」
--
-- 本模块分两步, 第二步是**对陈述本身的诊断**:
--
--   §1 ∀-字段**确有非平凡实例**: 取 Qphase θ x = phaseDiff zero θ x (相位输运本身),
--      transport θ x = mulAlpha (Qphase θ x) (pressurePhase θ x),
--      则 coupling 律**按定义相等 (refl)** 成立; 且 Qphase **非常数**
--      (见证 θ-e1 在原点取值 a1 ≠ a0) ⇒ 实例非平凡。
--      ⇒ §4d 的「∀-字段无实例」**不确切**。
--
--   §2 但更强的定理说明 **O2 是「错的问题」**: 对**任意** transport, 都存在 Qphase
--      使 coupling 律成立 (Qphase 由 transport 与压力的逆**解出**)。
--      原因是 `transport` 与 `Qphase` 都是 record 的**自由字段**, 记录**欠约束** ——
--      该方程从未约束任何东西。⇒ O2 按字面读作「是否存在实例」时答案是**恒真**。
--
--   §3 裁决: O2 的原陈述 = **statement_wrong**。要让 Madelung 耦合有内容, 必须
--      **约束 Qphase** 使之由场 ψ 决定 (物理上应为密度层的离散量子势
--      `quantumPotentialPhase`); 该受约束版**可被反例击穿**
--      (模块 :350 记:「真正非平凡的耦合方程对任意 θ 不成立 (反例 θ-e1-e2 在原点)」)
--      —— 那才是一个真问题。受约束义务另立台账节点。
--
-- 诚实边界: 本模块**不**声称离散 Madelung 方程成立或失败; 它只判定
--   「O2 的原陈述是否构成有意义的问题」—— 答案是否, 并给出重述方向。
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSEMadelungNonTrivial where

open import Data.Product using (Σ; _,_)
open import Data.Fin using (zero)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong)

open import Sovereign.Algebra.GroupTheory.DuodecClock using (
  AlphaPower; a0; a1; a2; a3; mulAlpha; alphaInv;
  mulAlpha-assoc; mulAlpha-identityʳ; mulAlpha-inverse)
open import Sovereign.Problem.NavierStokes.NSEPhaseField using (
  PhField; phaseDiff; pressurePhase; MadelungCoupling;
  theta-e1; origin6; phaseDiff-e1-zero)

--------------------------------------------------------------------------------
-- §0. 一条局部逆律 (左逆), 由 C₄ 表逐 case 给出
--
-- 库内 `mulAlpha-inverse : ∀ x → mulAlpha x (alphaInv x) ≡ a0` 是**右**逆;
-- 下面需要的是 `alphaInv p · p ≡ a0`。C₄ 只有 4 个元素, 逐 case 即可。
--------------------------------------------------------------------------------

alphaInv-invˡ : ∀ p → mulAlpha (alphaInv p) p ≡ a0
alphaInv-invˡ a0 = refl
alphaInv-invˡ a1 = refl
alphaInv-invˡ a2 = refl
alphaInv-invˡ a3 = refl

--------------------------------------------------------------------------------
-- §1. ∀-字段的非平凡实例
--------------------------------------------------------------------------------

-- 非平凡的相位量子势: 直接把相位输运当量子势
QphaseNT : PhField → PhField
QphaseNT θ x = phaseDiff zero θ x

-- 与之匹配的输运: 按 Qphase · pressurePhase 定义
transportNT : PhField → PhField
transportNT θ x = mulAlpha (QphaseNT θ x) (pressurePhase θ x)

-- ∀-字段的实例: coupling 由 refl 给出 (两侧正规形相同)
madelung-nontrivial : MadelungCoupling
madelung-nontrivial = record
  { transport = transportNT
  ; Qphase    = QphaseNT
  ; coupling  = λ θ x → refl
  }

-- QphaseNT **非常数** (故实例非平凡):
-- 见证 θ-e1 在原点取值 a1 ≠ a0 (库内 phaseDiff-e1-zero 由 refl 证, 归约后即 a1)
QphaseNT-nontrivial : QphaseNT theta-e1 origin6 ≢ a0
QphaseNT-nontrivial ()

--------------------------------------------------------------------------------
-- §2. 更强的判定: 耦合律对**任意** transport 都可解出 Qphase
--
-- 解: Qphase θ x := transport θ x · (pressurePhase θ x)⁻¹
-- 验算: (t · p⁻¹) · p = t · (p⁻¹ · p) = t · 1 = t   (结合律 + §0 左逆 + 单位律)
--------------------------------------------------------------------------------

solveQ : (PhField → PhField) → PhField → PhField
solveQ t θ x = mulAlpha (t θ x) (alphaInv (pressurePhase θ x))

-- 核心代数引理: (t · p⁻¹) · p ≡ t
-- 用显式 trans/cong 写 (不用 ≡-Reasoning 链): 结合律 → 左逆 → 单位律
solve-lemma : ∀ (t p : AlphaPower) → mulAlpha (mulAlpha t (alphaInv p)) p ≡ t
solve-lemma t p =
  trans (mulAlpha-assoc t (alphaInv p) p)
        (trans (cong (λ z → mulAlpha t z) (alphaInv-invˡ p))
               (mulAlpha-identityʳ t))

-- 主判定: 任何 transport 都能配到一个 Qphase 使耦合律成立
madelung-always-solvable : (t : PhField → PhField) →
  Σ (PhField → PhField)
    (λ Q → ∀ θ x → t θ x ≡ mulAlpha (Q θ x) (pressurePhase θ x))
madelung-always-solvable t =
  solveQ t , (λ θ x → sym (solve-lemma (t θ x) (pressurePhase θ x)))

--------------------------------------------------------------------------------
-- §3. 结论 (供 O2 的重述使用, 见模块头)
--
-- 由 §1 与 §2: 「MadelungCoupling 的 ∀-字段」**不是**筛选条件 ——
-- 它对任何 transport 都成立。故:
--   ✓ O2 读作「是否存在(非平凡)实例」 ⇒ **恒真**, 无数学内容 (本模块已证);
--   ✓ O2 要有内容 ⇒ 必须**约束 Qphase** 由密度层的离散量子势给出
--      (`quantumPotentialPhase`), 而不是自由参数。
--   ✓ 受约束版可被反例击穿 (:350 的反例 θ-e1-e2 在原点) ⇒ 它是**真问题**。
--
-- 裁决: O2 原陈述 = statement_wrong; 重述后的受约束义务另立台账节点。
--------------------------------------------------------------------------------
