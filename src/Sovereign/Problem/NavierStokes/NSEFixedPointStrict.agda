{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSEFixedPointStrict
-- 不动点集 **严格大于** 不可压子空间 + 支撑集可观察量的定义交付
--
-- 两件交付（判型先行, 均过可陈述性筛）:
--
-- ① **严格性定理**（本模块 §1–§3）:
--   `NSEFixedPoint` 证了「不可压 ⇒ 逐点不动」; 本模块给出**反向不成立**的见证:
--   斜坡场 `slope`（首坐标值场）满足 `div slope ≡ T₁`（**常非零**）⇒ 可压;
--   但 `grad (div slope)` 的各分量 = `diffF i (const T₁) ≡ T₀` ⇒ **逐点不动**。
--   ⇒ **不动点集 ⊋ 不可压子空间**（严格包含）。
--
-- ② **O3 通道 ⑤ 的缺失定义**（§4）: `supportCount : Field → ℕ`
--   （非零分量计数, 6 层 ℕ 折叠）——「支撑集/集中度」的可陈述性筛结果:
--     ⑤a 支撑集计数 **可陈述**（ℕ 值）⇒ 本模块交付定义;
--     ⑤b 峰值集中度 **不可陈述**（无序, 已在 O3 通道 ② 排除, 不重复）。
--   ⚠ **单调性/集中定理仍开放**（需对 `nsStep` 证界或非单调性）——只交定义, 不冒充。
--
-- 结构（0 postulate / 0 hole）:
--   §1 斜坡场 slopeField 与 `slope-diff`（3 case: fin3ToTrit ∘ shift3 的差商恒为 T₁）
--   §2 `div-slope-const`（6 元组模式 + sum6-cong）与 `diffF-of-const`
--   §3 `nsStep-fixed-gen`（N​SEFixedPoint.nsStep-fixed 的推广形态）+ **严格性定理**
--   §4 supportCount 定义 + 诚实边界
--
-- ⚠ 构造子纪律（流水 235 二犯教训）: 本模块同时用 `Data.Nat` 与 `Data.Fin` 的
--   构造子 —— Fin 侧 renaming 成 `fzero`/`fsuc`, 凡轴/坐标一律 `fzero`/`fsuc`,
--   凡计数递归一律 `zero`/`suc`（ℕ）—— 写前已全文核对裸构造子。
--
-- 依赖: NSEOnT6 / NSEFixedPoint（comp/axisOf）/ NSEConservation（sum6-cong）/ Base.Trit

module Sovereign.Problem.NavierStokes.NSEFixedPointStrict where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)
open import Relation.Nullary using (¬_)

open import Sovereign.Base.Trit using
  (Trit; T₀; T₁; T₂; _⊕_; negate; fin3ToTrit; ⊕-identityʳ)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6; mkField; zeroField;
   sum6; shift3; shiftAt; diffF; _+S_; _+F_; div; grad; nsStep; Incompressible)
open import Sovereign.Problem.NavierStokes.NSEConservation using (sum6-cong)
open import Sovereign.Problem.NavierStokes.NSEFixedPoint using (comp; axisOf)

--------------------------------------------------------------------------------
-- §1. 斜坡场: 首坐标的 Trit 值场（零场分量 ×5）
--------------------------------------------------------------------------------

zeroS : ScalarField
zeroS _ = T₀

slope : ScalarField
slope (c1 , c2 , c3 , c4 , c5 , c6) = fin3ToTrit c1

slopeField : Field
slopeField = mkField slope zeroS zeroS zeroS zeroS zeroS

-- 首坐标差商恒为 T₁（3 case; shift3 的 0→1→2→0 轮转给出恒定单位差）
slope-diff : ∀ (c : C3) → fin3ToTrit (shift3 c) ⊕ negate (fin3ToTrit c) ≡ T₁
slope-diff fzero               = refl
slope-diff (fsuc fzero)        = refl
slope-diff (fsuc (fsuc fzero)) = refl

--------------------------------------------------------------------------------
-- §2. div slope ≡ T₁（常非零 ⇒ 可压）; 常值场的一阶差分为零
--------------------------------------------------------------------------------

div-slope-const : ∀ (x : Torus6) → div slopeField x ≡ T₁
div-slope-const (c1 , c2 , c3 , c4 , c5 , c6) =
  trans (sum6-cong (slope-diff c1) t0 t0 t0 t0 t0) refl
  where
    -- 零分量项归约到 T₀; 显式标注钉住 sum6-cong 的隐式参数（refl 裸传会留元变量）
    t0 : T₀ ⊕ negate T₀ ≡ T₀
    t0 = refl

diffF-of-const : ∀ (i : C3) (g : ScalarField) (x : Torus6) →
  (∀ y → g y ≡ T₁) → g (shiftAt i x) ⊕ negate (g x) ≡ T₀
diffF-of-const i g x p rewrite p (shiftAt i x) | p x = refl

-- div slope 的差分恒零 ⇒ grad (div slope) 的每分量恒零
grad-of-const : ∀ (i : C3) (x : Torus6) → diffF i (div slopeField) x ≡ T₀
grad-of-const i x = diffF-of-const i (div slopeField) x div-slope-const

--------------------------------------------------------------------------------
-- §3. nsStep 不动点的推广形态 + **严格性定理**
--------------------------------------------------------------------------------

nsStep-fixed-gen : ∀ (v : Field) (s : ScalarField) →
  (∀ i x → diffF i s x ≡ T₀) →
  ∀ (k : Fin 6) (x : Torus6) → comp k (v +F grad s) x ≡ comp k v x
nsStep-fixed-gen v s h fzero x =
  trans (cong (v1 v x ⊕_) (h (axisOf fzero) x)) (⊕-identityʳ (v1 v x))
nsStep-fixed-gen v s h (fsuc fzero) x =
  trans (cong (v2 v x ⊕_) (h (axisOf (fsuc fzero)) x)) (⊕-identityʳ (v2 v x))
nsStep-fixed-gen v s h (fsuc (fsuc fzero)) x =
  trans (cong (v3 v x ⊕_) (h (axisOf (fsuc (fsuc fzero))) x)) (⊕-identityʳ (v3 v x))
nsStep-fixed-gen v s h (fsuc (fsuc (fsuc fzero))) x =
  trans (cong (v4 v x ⊕_) (h (axisOf (fsuc (fsuc (fsuc fzero)))) x)) (⊕-identityʳ (v4 v x))
nsStep-fixed-gen v s h (fsuc (fsuc (fsuc (fsuc fzero)))) x =
  trans (cong (v5 v x ⊕_) (h (axisOf (fsuc (fsuc (fsuc (fsuc fzero))))) x)) (⊕-identityʳ (v5 v x))
nsStep-fixed-gen v s h (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x =
  trans (cong (v6 v x ⊕_) (h (axisOf (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) x))
        (⊕-identityʳ (v6 v x))

-- 斜坡场: 可压（div ≡ T₁ ≠ T₀）
t1≢t0 : T₁ ≢ T₀
t1≢t0 ()

slope-compressible : ¬ Incompressible slopeField
slope-compressible inc = t1≢t0 (inc (fzero , fzero , fzero , fzero , fzero , fzero))

-- 斜坡场: 逐点不动（div 的差分恒零 ⇒ 演化步无事发生）
slope-is-fixed : ∀ (k : Fin 6) (x : Torus6) →
  comp k (nsStep slopeField) x ≡ comp k slopeField x
slope-is-fixed = nsStep-fixed-gen slopeField (div slopeField) grad-of-const

-- **主定理**: 不动点集 **严格大于** 不可压子空间
fixed-point-set-strict : Σ Field (λ v →
  (¬ Incompressible v) × (∀ k x → comp k (nsStep v) x ≡ comp k v x))
fixed-point-set-strict = slopeField , (slope-compressible , slope-is-fixed)

--------------------------------------------------------------------------------
-- §4. O3 通道 ⑤: 支撑集可观察量的定义（可陈述性筛: ⑤a ✓ / ⑤b ✗ 已在 ② 排除）
--------------------------------------------------------------------------------

isNonZero : Trit → ℕ
isNonZero T₀ = zero
isNonZero T₁ = suc zero
isNonZero T₂ = suc zero

fold1N : (C3 → ℕ) → ℕ
fold1N g = g fzero + (g (fsuc fzero) + g (fsuc (fsuc fzero)))

-- 单分量的非零点计数（729 点; 6 层 ℕ 折叠）
countOver : ScalarField → ℕ
countOver f = fold1N (λ x1 → fold1N (λ x2 → fold1N (λ x3 →
              fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 →
                isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))))))

-- **支撑集可观察量**（O3 通道 ⑤ 的缺失定义; 全场 = 6 分量之和, 上界 6 × 729 = 4374）
supportCount : Field → ℕ
supportCount v = countOver (v1 v) + (countOver (v2 v) + (countOver (v3 v)
                 + (countOver (v4 v) + (countOver (v5 v) + countOver (v6 v)))))

--------------------------------------------------------------------------------
-- §5. 诚实边界
--
-- ✓ 已证: §1–§3（斜坡场见证 + 严格性定理）; §4 是**定义交付**。
-- ✗ 不声称（O3 通道 ⑤ **仍开放**）:
--   ① supportCount 的**界**（0 ≤ c ≤ 4374）未证（ℕ 界引理待补）;
--   ② supportCount 在 nsStep 下的**单调性/非单调性**未证（集中度定理本体）;
--   ③ 不动点集的**完整刻画**（只证了「⊋」的严格性, 未刻画全体不动点);
--   ④ 连续统 NS 的任何结论（不主张连续极限）。
--
-- 对抗验证: 零场在不动点集内（`NSEFixedPoint` 侧）; 斜坡场在不动点集内但在
-- 不可压子空间外（本模块 §3）—— 两侧实例共同锚定「⊋」。
--------------------------------------------------------------------------------
