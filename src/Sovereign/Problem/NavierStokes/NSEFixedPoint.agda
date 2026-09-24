{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEFixedPoint
-- **不可压子空间 = nsStep 的不动点集**（逐点版）
--
-- 主定理（本模块）:
--   `nsStep-fixed : ∀ v → Incompressible v → ∀ k x → comp k (nsStep v) x ≡ comp k v x`
--   **推论** `iterate-fixed : ∀ n v → Incompressible v → ∀ k x →
--              comp k (iterate n nsStep v) x ≡ comp k v x`
--   ⇒ 不可压场的轨道是**常值轨道**（周期 1）——该离散 N-S 格式在不可压子空间上
--   **没有时间演化**。物理读法: 「多步集中」在不可压子空间上**根本不存在**
--   （不是被限制, 是无事发生）; 对可压流, 总量/有界/最终周期仍限制一切。
--
-- 推导（逐点）: nsStep v 的第 k 分量 = v_k x ⊕ diffF (axis k) (div v) x
--   · 不可压 ⇒ diffF (axis k) (div v) x ≡ T₀（`diffF-zero-at`, 两处 rewrite）
--   · ⇒ 分量值 = v_k x ⊕ T₀ ≡ v_k x（`⊕-identityʳ`）
--
-- 结构（0 postulate / 0 hole）:
--   §1 分量选择器 comp / 轴选择器 axisOf（各 6 case, 对齐 grad 的六分量布局
--       NSEOnT6:534-536 = 轴 0/1/2 各两次）
--   §2 `diffF-zero-at`（点态零场的一阶差分为零）
--   §3 **主定理** `nsStep-fixed`（6 case）
--   §4 **推论** `iterate-fixed`（归纳）
--   §5 对抗验证与诚实边界
--
-- ⚠ 诚实边界: ① 逐点相等（本库无 funext, 不写 Field 整体相等——逐点即标准形态）;
--   ② 只刻画**不可压子空间**; 可压流的再分布/集中度**仍开放**;
--   ③ 非连续统结论（不主张连续极限）。
--
-- 依赖: NSEOnT6（Field/v₁…v₆/diffF/shiftAt/div/grad/nsStep/Incompressible/iterate）,
--       NSEIncompressible（nsStep-incompressible, 供归纳步取用）

module Sovereign.Problem.NavierStokes.NSEFixedPoint where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using
  (_≡_; refl; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-identityʳ)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6;
   shiftAt; diffF; div; grad; nsStep; Incompressible; iterate)
open import Sovereign.Problem.NavierStokes.NSEIncompressible using (nsStep-incompressible)

--------------------------------------------------------------------------------
-- §1. 分量与轴的选择器（对齐 grad 六分量 = 轴 0/1/2 各两次）
--------------------------------------------------------------------------------

comp : Fin 6 → Field → ScalarField
comp fzero                    = v1
comp (fsuc fzero)             = v2
comp (fsuc (fsuc fzero))      = v3
comp (fsuc (fsuc (fsuc fzero)))               = v4
comp (fsuc (fsuc (fsuc (fsuc fzero))))        = v5
comp (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = v6

axisOf : Fin 6 → C3
axisOf fzero                    = fzero
axisOf (fsuc fzero)             = fsuc fzero
axisOf (fsuc (fsuc fzero))      = fsuc (fsuc fzero)
axisOf (fsuc (fsuc (fsuc fzero)))               = fzero
axisOf (fsuc (fsuc (fsuc (fsuc fzero))))        = fsuc fzero
axisOf (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = fsuc (fsuc fzero)

--------------------------------------------------------------------------------
-- §2. 点态零场的一阶差分为零
--------------------------------------------------------------------------------

diffF-zero-at : ∀ (i : C3) (g : ScalarField) (x : Torus6) →
  (∀ y → g y ≡ T₀) → g (shiftAt i x) ⊕ negate (g x) ≡ T₀
diffF-zero-at i g x p rewrite p (shiftAt i x) | p x = refl

--------------------------------------------------------------------------------
-- §3. 主定理: 不可压场逐点不动（6 case）
--------------------------------------------------------------------------------

nsStep-fixed : ∀ (v : Field) → Incompressible v →
  ∀ (k : Fin 6) (x : Torus6) → comp k (nsStep v) x ≡ comp k v x
nsStep-fixed v inc fzero x =
  trans (cong (v1 v x ⊕_) (diffF-zero-at fzero (div v) x inc))
        (⊕-identityʳ (v1 v x))
nsStep-fixed v inc (fsuc fzero) x =
  trans (cong (v2 v x ⊕_) (diffF-zero-at (fsuc fzero) (div v) x inc))
        (⊕-identityʳ (v2 v x))
nsStep-fixed v inc (fsuc (fsuc fzero)) x =
  trans (cong (v3 v x ⊕_) (diffF-zero-at (fsuc (fsuc fzero)) (div v) x inc))
        (⊕-identityʳ (v3 v x))
nsStep-fixed v inc (fsuc (fsuc (fsuc fzero))) x =
  trans (cong (v4 v x ⊕_) (diffF-zero-at fzero (div v) x inc))
        (⊕-identityʳ (v4 v x))
nsStep-fixed v inc (fsuc (fsuc (fsuc (fsuc fzero)))) x =
  trans (cong (v5 v x ⊕_) (diffF-zero-at (fsuc fzero) (div v) x inc))
        (⊕-identityʳ (v5 v x))
nsStep-fixed v inc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x =
  trans (cong (v6 v x ⊕_) (diffF-zero-at (fsuc (fsuc fzero)) (div v) x inc))
        (⊕-identityʳ (v6 v x))

--------------------------------------------------------------------------------
-- §4. 推论: n 步迭代仍是同一场（常值轨道）
--------------------------------------------------------------------------------

iterate-fixed : ∀ (n : ℕ) (v : Field) → Incompressible v →
  ∀ (k : Fin 6) (x : Torus6) → comp k (iterate n nsStep v) x ≡ comp k v x
iterate-fixed zero v inc k x = refl
iterate-fixed (suc n) v inc k x =
  trans (iterate-fixed n (nsStep v) (nsStep-incompressible v inc) k x)
        (nsStep-fixed v inc k x)

--------------------------------------------------------------------------------
-- §5. 对抗验证与诚实边界
--
-- 对抗验证（纪律 §6）: zeroField 不可压（NSEIncompressible.zeroField-incompressible）
--   且逐点不动 —— `nsStep-fixed zeroField …` 的两侧均归约到 T₀, 与直觉一致。
--   （此处不另写 refl 条目: 主定理已是逐点等式, 其类型本身就是对照。）
--
-- ✓ 已证: §2/§3/§4（全部构造性）。
-- ✗ 不声称:
--   ① Field 整体相等（需 funext; 逐点相等是本库的标准形态）;
--   ② 可压流的再分布/集中度 —— **仍开放**（O3 的支撑集/集中度定理）;
--   ③ 连续统 NS 的任何结论。
--------------------------------------------------------------------------------
