{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSESupportFixedInv
-- supportCount 在不动点集上不变（O3 通道 ⑤ 的「不变性」增量）
--
-- 主定理:
--   `supportCount-nsStep-inv : (∀ k x → comp k (nsStep v) x ≡ comp k v x) →
--                              supportCount (nsStep v) ≡ supportCount v`
--   推论（对抗验证）: 不可压场（`NSEFixedPoint.nsStep-fixed`）与斜坡场
--   （`NSEFixedPointStrict.slope-is-fixed`）的 supportCount 在一步演化下恒定。
--
-- ⑤ 的四件套现状: 定义（FixedPointStrict）+ 界（SupportBound）+ 零元刻画（SupportZero）
--   + **不动点处不变（本模块）**；**单调性/再分布半仍开放**（非不动点上的变化规律
--   = 集中度定理本体）。
--
-- 通用件（本模块交付, 复用于后续 n 步版）:
--   `countOver-ext`    : 逐点相等 ⇒ 计数相等（where 具名 ez1…ez6 钉死 g/g'）
--   `supportCount-ext` : 分量逐点相等 ⇒ 全场计数相等
--
-- ⚠ 陷阱预警（三条已入册 memory/nse-invariant-campaign.md §3）:
--   ① **非单射的定义函数不传 `_`/隐式**（元变量陷阱）；② Fin 侧 `fzero`/`fsuc`、
--   ℕ 侧 `zero`/`suc`；③ 长重写后先扫构造子拼写。
--
-- 0 postulate / 0 hole

module Sovereign.Problem.NavierStokes.NSESupportFixedInv where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6; nsStep; iterate; Incompressible)
open import Sovereign.Problem.NavierStokes.NSEFixedPoint using
  (comp; nsStep-fixed; iterate-fixed)
open import Sovereign.Problem.NavierStokes.NSEFixedPointStrict using
  (isNonZero; fold1N; countOver; supportCount; slopeField; slope-is-fixed)
open import Sovereign.Problem.NavierStokes.NSESupportZero using (fold1N-cong; plus6-cong)

--------------------------------------------------------------------------------
-- §1. 逐点相等 ⇒ 计数相等
--------------------------------------------------------------------------------

countOver-ext : ∀ (f g : ScalarField) → (∀ x → f x ≡ g x) → countOver f ≡ countOver g
countOver-ext f g p = ez1
  where
    -- 逐层具名: **签名钉死 g/g'**, 规避隐式参数的元变量陷阱
    ez6 : ∀ x1 x2 x3 x4 x5 →
      fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))
      ≡ fold1N (λ x6 → isNonZero (g (x1 , x2 , x3 , x4 , x5 , x6)))
    ez6 x1 x2 x3 x4 x5 =
      fold1N-cong (λ x6 → cong isNonZero (p (x1 , x2 , x3 , x4 , x5 , x6)))

    ez5 : ∀ x1 x2 x3 x4 →
      fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))
      ≡ fold1N (λ x5 → fold1N (λ x6 → isNonZero (g (x1 , x2 , x3 , x4 , x5 , x6))))
    ez5 x1 x2 x3 x4 = fold1N-cong (λ x5 → ez6 x1 x2 x3 x4 x5)

    ez4 : ∀ x1 x2 x3 →
      fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))
      ≡ fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (g (x1 , x2 , x3 , x4 , x5 , x6)))))
    ez4 x1 x2 x3 = fold1N-cong (λ x4 → ez5 x1 x2 x3 x4)

    ez3 : ∀ x1 x2 →
      fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))))
      ≡ fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (g (x1 , x2 , x3 , x4 , x5 , x6))))))
    ez3 x1 x2 = fold1N-cong (λ x3 → ez4 x1 x2 x3)

    ez2 : ∀ x1 →
      fold1N (λ x2 → fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))))
      ≡ fold1N (λ x2 → fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (g (x1 , x2 , x3 , x4 , x5 , x6)))))))
    ez2 x1 = fold1N-cong (λ x2 → ez3 x1 x2)

    ez1 : countOver f ≡ countOver g
    ez1 = fold1N-cong (λ x1 → ez2 x1)

--------------------------------------------------------------------------------
-- §2. 分量逐点相等 ⇒ 全场计数相等
--------------------------------------------------------------------------------

supportCount-ext : ∀ (v w : Field) → (∀ k x → comp k v x ≡ comp k w x) →
  supportCount v ≡ supportCount w
supportCount-ext v w h =
  plus6-cong
    (countOver-ext (v1 v) (v1 w) (λ x → h fzero x))
    (countOver-ext (v2 v) (v2 w) (λ x → h (fsuc fzero) x))
    (countOver-ext (v3 v) (v3 w) (λ x → h (fsuc (fsuc fzero)) x))
    (countOver-ext (v4 v) (v4 w) (λ x → h (fsuc (fsuc (fsuc fzero))) x))
    (countOver-ext (v5 v) (v5 w) (λ x → h (fsuc (fsuc (fsuc (fsuc fzero)))) x))
    (countOver-ext (v6 v) (v6 w) (λ x → h (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x))

--------------------------------------------------------------------------------
-- §3. 主定理: supportCount 在不动点集上不变
--------------------------------------------------------------------------------

supportCount-nsStep-inv : ∀ (v : Field) →
  (∀ k x → comp k (nsStep v) x ≡ comp k v x) →
  supportCount (nsStep v) ≡ supportCount v
supportCount-nsStep-inv v h = supportCount-ext (nsStep v) v h

--------------------------------------------------------------------------------
-- §4. 推论与对抗验证（两个具体实例）
--------------------------------------------------------------------------------

-- 不可压场: supportCount 在一步演化下恒定（NSEFixedPoint.nsStep-fixed）
supportCount-incompressible-inv : ∀ (v : Field) → Incompressible v →
  supportCount (nsStep v) ≡ supportCount v
supportCount-incompressible-inv v inc =
  supportCount-nsStep-inv v (λ k x → nsStep-fixed v inc k x)

-- 斜坡场: 可压不动点的 supportCount 同样恒定（NSEFixedPointStrict.slope-is-fixed）
supportCount-slope-inv : supportCount (nsStep slopeField) ≡ supportCount slopeField
supportCount-slope-inv = supportCount-nsStep-inv slopeField slope-is-fixed

-- 不可压场: **n 步版**（`NSEFixedPoint.iterate-fixed` 的点态形态直接给出）
supportCount-iterate-inv : ∀ (n : ℕ) (v : Field) → Incompressible v →
  supportCount (iterate n nsStep v) ≡ supportCount v
supportCount-iterate-inv n v inc =
  supportCount-ext (iterate n nsStep v) v (λ k x → iterate-fixed n v inc k x)

--------------------------------------------------------------------------------
-- §5. 诚实边界
--
-- ✓ 已证: countOver-ext / supportCount-ext / **supportCount-nsStep-inv**
--   / 两个具体推论。
-- ✗ 不声称（⑤ 仍开放的部分）:
--   ① supportCount 在 **n 步**迭代下的不变（需 `nsStep-ext` 型引理做归纳前提，
--      或用 `NSEFixedPoint.iterate-fixed` 的点态形态直接推——**待补**）;
--   ② supportCount 在**非不动点**上的单调性/非单调性（集中度定理本体）;
--   ③ 「不变性 ⇒ 无集中」**不成立**（不动点外的变化规律仍未描述）;
--   ④ 连续统 NS 的任何结论。
--------------------------------------------------------------------------------
