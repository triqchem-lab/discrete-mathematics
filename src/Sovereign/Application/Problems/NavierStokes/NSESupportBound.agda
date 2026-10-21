{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Application.Problems.NavierStokes.NSESupportBound
-- 支撑集可观察量的**双界**: countOver ≤ 729; supportCount ≤ 4374
--
-- 背景: O3 通道 ⑤（再分布/集中度）的「界」半。`NSEFixedPointStrict` 交付了
--   缺失定义 `supportCount : Field → ℕ`（非零分量计数）; 本模块给出它的**双界**。
--   ⑤ 的**单调性半仍开放**（supportCount 在 nsStep 下的单调/非单调 = 集中度定理本体）。
--
-- 结构（0 postulate / 0 hole）:
--   §1 `isNonZero-≤1`（3 case: 计数每点至多 1）
--   §2 `fold1N-mono`（单调提升; `+-mono-≤` 一次给出）
--   §3 **双界** `countOver-bound ≤ 729` / `supportCount-bound ≤ 4374`
--     （6 层单调提升 + `≤-reflexive refl` 吃掉常数折叠的 3⁶=729 与 6×729=4374）
--   §4 诚实边界
--
-- 判型注: 本模块是 **ℕ 半序上的结构证明**（单调提升 + 常数计算）——
--   既非配对弹出的相消型/置换型, 也非表事实; 不适用穷举, 也不需要弹出。
--
-- ⚠ 构造子纪律（流水 235 教训）: Fin 侧一律 `fzero`/`fsuc`, ℕ 侧一律 `zero`/`suc`。
--
-- 依赖: NSEFixedPointStrict（isNonZero/fold1N/countOver/supportCount）; Data.Nat.Properties

module Sovereign.Application.Problems.NavierStokes.NSESupportBound where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; +-mono-≤; m+n≡0⇒m≡0; m+n≡0⇒n≡0)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Application.Problems.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6)
open import Sovereign.Application.Problems.NavierStokes.NSEFixedPointStrict using
  (isNonZero; fold1N; countOver; supportCount)

--------------------------------------------------------------------------------
-- §1. 每点计数 ≤ 1
--------------------------------------------------------------------------------

isNonZero-≤1 : ∀ (t : Trit) → isNonZero t ≤ suc zero
isNonZero-≤1 T₀ = z≤n
isNonZero-≤1 T₁ = s≤s z≤n
isNonZero-≤1 T₂ = s≤s z≤n

--------------------------------------------------------------------------------
-- §2. fold1N 的单调提升
--------------------------------------------------------------------------------

fold1N-mono : ∀ {g g' : C3 → ℕ} → (∀ y → g y ≤ g' y) → fold1N g ≤ fold1N g'
fold1N-mono {g} {g'} p =
  +-mono-≤ (p fzero) (+-mono-≤ (p (fsuc fzero)) (p (fsuc (fsuc fzero))))

--------------------------------------------------------------------------------
-- §3. 双界
--------------------------------------------------------------------------------

-- ① 单分量非零点数 ≤ 729 = 3⁶
countOver-bound : ∀ (f : ScalarField) → countOver f ≤ 729
countOver-bound f =
  ≤-trans
    (fold1N-mono (λ x1 → fold1N-mono (λ x2 → fold1N-mono (λ x3 →
       fold1N-mono (λ x4 → fold1N-mono (λ x5 → fold1N-mono (λ x6 →
         isNonZero-≤1 (f (x1 , x2 , x3 , x4 , x5 , x6)))))))))
    (≤-reflexive refl)

-- ② 全场非零分量总数 ≤ 4374 = 6 × 729
supportCount-bound : ∀ (v : Field) → supportCount v ≤ 4374
supportCount-bound v =
  ≤-trans
    (+-mono-≤ (countOver-bound (v1 v))
      (+-mono-≤ (countOver-bound (v2 v))
        (+-mono-≤ (countOver-bound (v3 v))
          (+-mono-≤ (countOver-bound (v4 v))
            (+-mono-≤ (countOver-bound (v5 v)) (countOver-bound (v6 v)))))))
    (≤-reflexive refl)

--------------------------------------------------------------------------------
-- §4. 诚实边界
--
-- ✓ 已证: `isNonZero-≤1` / `fold1N-mono` / **countOver-bound ≤ 729** /
--   **supportCount-bound ≤ 4374**（全部构造性; 末步为字面归约 3⁶=729、6·729=4374）。
-- ✗ 不声称（O3 通道 ⑤ **仍开放的部分**）:
--   ① supportCount 在 `nsStep` 下的**单调性/非单调性**（集中度定理本体）;
--   ② supportCount 的**下界**与零场刻画（supportCount v ≡ 0 ↔ v ≈ 0）——未证;
--   ③ 「界 ⇒ 无集中」**不成立**（有界仍允许再分布）;
--   ④ 连续统 NS 的任何结论。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §5. ★ 零场刻画（标量场）：`countOver f ≡ 0 ↔ f` 处处为零
--------------------------------------------------------------------------------

isNonZero-zero : ∀ t → isNonZero t ≡ 0 → t ≡ T₀
isNonZero-zero T₀ e = refl
isNonZero-zero T₁ ()
isNonZero-zero T₂ ()

fold1N-zero : ∀ (g : C3 → ℕ) → fold1N g ≡ 0 → ∀ y → g y ≡ 0
fold1N-zero g e fzero = m+n≡0⇒m≡0 (g fzero) e
fold1N-zero g e (fsuc fzero) = m+n≡0⇒m≡0 (g (fsuc fzero)) (m+n≡0⇒n≡0 (g fzero) e)
fold1N-zero g e (fsuc (fsuc fzero)) =
  m+n≡0⇒n≡0 (g (fsuc fzero)) (m+n≡0⇒n≡0 (g fzero) e)

G6 : ScalarField → C3 → C3 → C3 → C3 → C3 → C3 → ℕ
G6 f y1 y2 y3 y4 y5 y6 = isNonZero (f (y1 , y2 , y3 , y4 , y5 , y6))
G5 : ScalarField → C3 → C3 → C3 → C3 → C3 → ℕ
G5 f y1 y2 y3 y4 y5 = fold1N (G6 f y1 y2 y3 y4 y5)
G4 : ScalarField → C3 → C3 → C3 → C3 → ℕ
G4 f y1 y2 y3 y4 = fold1N (G5 f y1 y2 y3 y4)
G3 : ScalarField → C3 → C3 → C3 → ℕ
G3 f y1 y2 y3 = fold1N (G4 f y1 y2 y3)
G2 : ScalarField → C3 → C3 → ℕ
G2 f y1 y2 = fold1N (G3 f y1 y2)
G1 : ScalarField → C3 → ℕ
G1 f y1 = fold1N (G2 f y1)

countOver-zero : ∀ (f : ScalarField) → countOver f ≡ 0
               → ∀ x1 x2 x3 x4 x5 x6 → f (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀
countOver-zero f e x1 x2 x3 x4 x5 x6 =
  isNonZero-zero _
    (fold1N-zero (G6 f x1 x2 x3 x4 x5)
      (fold1N-zero (G5 f x1 x2 x3 x4)
        (fold1N-zero (G4 f x1 x2 x3)
          (fold1N-zero (G3 f x1 x2)
            (fold1N-zero (G2 f x1)
              (fold1N-zero (G1 f) e x1) x2) x3) x4) x5) x6)

fold1N-cong : ∀ {g g' : C3 → ℕ} → (∀ y → g y ≡ g' y) → fold1N g ≡ fold1N g'
fold1N-cong p = cong₂ _+_ (p fzero) (cong₂ _+_ (p (fsuc fzero)) (p (fsuc (fsuc fzero))))

countOver-zero← : ∀ (f : ScalarField)
                → (∀ x1 x2 x3 x4 x5 x6 → f (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
                → countOver f ≡ 0
countOver-zero← f h =
  trans (fold1N-cong (λ y1 → fold1N-cong (λ y2 → fold1N-cong (λ y3 →
          fold1N-cong (λ y4 → fold1N-cong (λ y5 → fold1N-cong (λ y6 →
            cong isNonZero (h y1 y2 y3 y4 y5 y6)))))))) refl

--------------------------------------------------------------------------------
-- §6. ★★ Field 六分量：`supportCount v ≡ 0` ⇒ 每个分量场恒零（及反向）
--------------------------------------------------------------------------------

_SixZero : Field → Set
_SixZero v = (∀ x1 x2 x3 x4 x5 x6 → v1 v (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
           × ((∀ x1 x2 x3 x4 x5 x6 → v2 v (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
           × ((∀ x1 x2 x3 x4 x5 x6 → v3 v (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
           × ((∀ x1 x2 x3 x4 x5 x6 → v4 v (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
           × ((∀ x1 x2 x3 x4 x5 x6 → v5 v (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)
           × (∀ x1 x2 x3 x4 x5 x6 → v6 v (x1 , x2 , x3 , x4 , x5 , x6) ≡ T₀)))))

supportCount-zero : ∀ (v : Field) → supportCount v ≡ 0 → _SixZero v
supportCount-zero v e = z1 , (z2 , (z3 , (z4 , (z5 , z6))))
  where
    e1 = m+n≡0⇒m≡0 (countOver (v1 v)) e
    eR1 = m+n≡0⇒n≡0 (countOver (v1 v)) e
    e2 = m+n≡0⇒m≡0 (countOver (v2 v)) eR1
    eR2 = m+n≡0⇒n≡0 (countOver (v2 v)) eR1
    e3 = m+n≡0⇒m≡0 (countOver (v3 v)) eR2
    eR3 = m+n≡0⇒n≡0 (countOver (v3 v)) eR2
    e4 = m+n≡0⇒m≡0 (countOver (v4 v)) eR3
    eR4 = m+n≡0⇒n≡0 (countOver (v4 v)) eR3
    e5 = m+n≡0⇒m≡0 (countOver (v5 v)) eR4
    e6 = m+n≡0⇒n≡0 (countOver (v5 v)) eR4
    z1 = countOver-zero (v1 v) e1
    z2 = countOver-zero (v2 v) e2
    z3 = countOver-zero (v3 v) e3
    z4 = countOver-zero (v4 v) e4
    z5 = countOver-zero (v5 v) e5
    z6 = countOver-zero (v6 v) e6

supportCount-zero← : ∀ (v : Field) → _SixZero v → supportCount v ≡ 0
supportCount-zero← v (h1 , h2 , h3 , h4 , h5 , h6) =
  cong₂ _+_ (countOver-zero← (v1 v) h1)
    (cong₂ _+_ (countOver-zero← (v2 v) h2)
      (cong₂ _+_ (countOver-zero← (v3 v) h3)
        (cong₂ _+_ (countOver-zero← (v4 v) h4)
          (cong₂ _+_ (countOver-zero← (v5 v) h5) (countOver-zero← (v6 v) h6)))))
