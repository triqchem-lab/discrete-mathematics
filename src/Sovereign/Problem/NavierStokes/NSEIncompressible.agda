{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEIncompressible
-- **无条件**版不可压保持: `nsStep` 保持 `Incompressible`
--
-- 背景: `NSEOnT6:615` 的同名定理带前提 `(∀ f x → laplacian f x ≡ T₀)` ——
--   该前提已被 **T1 否证**（离散 Laplacian 不恒零, 见 NSE.T1/T2 反例链）⇒
--   旧定理是**条件式空转**（假前提下的一切都成立, 无信息）。
--   本模块用**真事实**去掉前提:
--     · `div-grad : div (grad s) ≡ laplacian s`（NSEOnT6:539, 定义性 refl）
--     · 不可压的**点态**条件 `∀ x → div v x ≡ T₀` ⇒ 每个轴向二阶差分逐点为零
--
-- 结构（0 postulate / 0 hole）:
--   §1 `plus-negate-zero`     : GF(3) 逆元律（3 case）
--   §2 `axisLap-zero-at`      : 点态零场的轴向二阶差分为零（展开形 + rewrite）
--   §3 `div-grad-zero`        : div (grad s) 点态为零（六个 summand 经 sum6-cong 汇总）
--   §4 `div-linear`           : div 的加法线性（diffF-+S ×6 + sum6-+）
--   §5 **主定理** `nsStep-incompressible`（无条件）+ 对抗验证（zeroField 实例）
--
-- 物理读法: **压缩型集中通道被封死** —— 不可压场经一步演化仍不可压。
--   与总量守恒（`NSEConservation.total-nsStep`）互补: 一个封「总量增减」,
--   一个封「压缩聚集」。二者都**不等于**「无集中」（再分布仍可能）。
--
-- ⚠ 诚实边界: 本模块只替换 NSEOnT6:615 的**空转条件式**; 不声称连续统 NS 的
--   不可压保持定理（那需要连续极限, 本框架不主张）。
--
-- 依赖: NSEOnT6（算子与 diffF-+/sum6-+/Incompressible）, NSEConservation（sum6-cong）

module Sovereign.Problem.NavierStokes.NSEIncompressible where

open import Data.Fin using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; negate; ⊕-identityʳ)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6; zeroField;
   sum6; shiftAt; shiftF; diffF; _+S_; _+F_; div; grad; nsStep; Incompressible;
   diffF-+S; sum6-+)
open import Sovereign.Problem.NavierStokes.NSEConservation using (sum6-cong)

--------------------------------------------------------------------------------
-- §1. GF(3) 逆元律
--------------------------------------------------------------------------------

plus-negate-zero : ∀ (a : Trit) → a ⊕ negate a ≡ T₀
plus-negate-zero T₀ = refl
plus-negate-zero T₁ = refl
plus-negate-zero T₂ = refl

--------------------------------------------------------------------------------
-- §2. 点态零场的轴向二阶差分为零
--
-- 取**展开形**（f (shiftAt …) 直写）, 使 `rewrite` 能看见三个求和位上的 g。
--------------------------------------------------------------------------------

axisLap-zero-at : ∀ (i : C3) (g : ScalarField) (x : Torus6) →
  (∀ y → g y ≡ T₀) →
  (g (shiftAt i (shiftAt i x)) ⊕ negate (g (shiftAt i x)))
    ⊕ negate (g (shiftAt i x) ⊕ negate (g x))
  ≡ T₀
axisLap-zero-at i g x p
  rewrite p x | p (shiftAt i x) | p (shiftAt i (shiftAt i x)) = refl

--------------------------------------------------------------------------------
-- §3. div (grad s) 点态为零
--
-- div (grad s) x 的定义体 = sum6 六个二阶差分（轴 0/1/2 各两次, 对应 grad 的
-- 六分量与 div 的求和顺序）; 逐项归零后 sum6 T₀×6 ≡ T₀（refl）。
--------------------------------------------------------------------------------

div-grad-zero : ∀ (s : ScalarField) (x : Torus6) →
  (∀ y → s y ≡ T₀) → div (grad s) x ≡ T₀
div-grad-zero s x p =
  trans (sum6-cong
           (axisLap-zero-at zero s x p)
           (axisLap-zero-at (suc zero) s x p)
           (axisLap-zero-at (suc (suc zero)) s x p)
           (axisLap-zero-at zero s x p)
           (axisLap-zero-at (suc zero) s x p)
           (axisLap-zero-at (suc (suc zero)) s x p))
        refl

--------------------------------------------------------------------------------
-- §4. div 的加法线性: div (u +F w) x ≡ div u x ⊕ div w x
--------------------------------------------------------------------------------

div-linear : ∀ (u w : Field) (x : Torus6) →
  div (u +F w) x ≡ div u x ⊕ div w x
div-linear u w x =
  trans (sum6-cong
           (diffF-+S zero (v1 u) (v1 w) x)
           (diffF-+S (suc zero) (v2 u) (v2 w) x)
           (diffF-+S (suc (suc zero)) (v3 u) (v3 w) x)
           (diffF-+S zero (v4 u) (v4 w) x)
           (diffF-+S (suc zero) (v5 u) (v5 w) x)
           (diffF-+S (suc (suc zero)) (v6 u) (v6 w) x))
        (sum6-+
           (diffF zero (v1 u) x) (diffF zero (v1 w) x)
           (diffF (suc zero) (v2 u) x) (diffF (suc zero) (v2 w) x)
           (diffF (suc (suc zero)) (v3 u) x) (diffF (suc (suc zero)) (v3 w) x)
           (diffF zero (v4 u) x) (diffF zero (v4 w) x)
           (diffF (suc zero) (v5 u) x) (diffF (suc zero) (v5 w) x)
           (diffF (suc (suc zero)) (v6 u) x) (diffF (suc (suc zero)) (v6 w) x))

--------------------------------------------------------------------------------
-- §5. 主定理（无条件）与对抗验证
--
-- 推导: div (nsStep v) x
--     ≡⟨div-linear⟩ div v x ⊕ div (grad (div v)) x
--     ≡⟨div-grad-zero⟩ div v x ⊕ T₀
--     ≡⟨⊕-identityʳ⟩ div v x
--     ≡⟨inc x⟩ T₀
--------------------------------------------------------------------------------

nsStep-incompressible : ∀ (v : Field) → Incompressible v → Incompressible (nsStep v)
nsStep-incompressible v inc x =
  trans (div-linear v (grad (div v)) x)
  (trans (cong (div v x ⊕_) (div-grad-zero (div v) x inc))
  (trans (⊕-identityʳ (div v x))
         (inc x)))

-- 对抗验证（纪律 §6）: 零场不可压（refl 独立核对）, 并经主定理闭合
zeroField-incompressible : Incompressible zeroField
zeroField-incompressible x = refl

nsStep-zeroField-incompressible : Incompressible (nsStep zeroField)
nsStep-zeroField-incompressible = nsStep-incompressible zeroField zeroField-incompressible

--------------------------------------------------------------------------------
-- §6. 诚实边界
--
-- ✓ 已证: **无条件** `nsStep-incompressible`（替换 NSEOnT6:615 的空转条件式）。
-- ✗ 不声称:
--   ① 不可压保持 ≠ 无集中 —— 只封「压缩型」通道, 再分布仍可能
--      （O3 完全闭合仍需支撑集/集中度定理）;
--   ② 不是连续统 NS 的不可压保持定理（需连续极限, 本框架不主张）;
--   ③ `NSEOnT6:615` 旧定理**未删改**（回执保护）, 只是不再引用——
--      其前提已被 T1 否证的事实记于本模块头。
--------------------------------------------------------------------------------
