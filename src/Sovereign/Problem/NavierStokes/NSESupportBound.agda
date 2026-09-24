{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSESupportBound
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

module Sovereign.Problem.NavierStokes.NSESupportBound where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; +-mono-≤)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6)
open import Sovereign.Problem.NavierStokes.NSEFixedPointStrict using
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
