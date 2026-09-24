{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Problem.NavierStokes.NSESupportZero
-- 支撑集可观察量的**零场刻画**: supportCount v ≡ 0 ⇔ 逐点全零
--
-- 背景: O3 通道 ⑤ 的「零元端」。`NSEFixedPointStrict` 交定义、`NSESupportBound` 交界;
--   本模块补**零元等价**（⑤ 的下界侧: supportCount 的最小值 0 的原像恰为零场）。
--   ⚠ ⑤ 的**单调性半仍开放**（supportCount 在 nsStep 下的单调/非单调 = 集中度定理本体）。
--
-- 结构（0 postulate / 0 hole）:
--   §1 `plus-zero-split`（ℕ 加法归零拆分; 自备, 免 stdlib 名字风险）
--   §2 `isNonZero-zero`（3 case）/ `fold1N-zero`（逐层提取）/ `countOver-zero`（6 层）
--   §3 `fold1N-cong`（3 个 cong）/ `countOver-all-zero`（6 层）/ `plus6-cong`（J 一次给出）
--   §4 **主定理** `supportCount-zero→` / `supportCount-zero←`
--   §5 诚实边界
--
-- ⚠ 陷阱记录（本模块踩到一次, 已修）: **`plus-zero-split _ _ p` 的下划线推不出来**——
--   `_+_` 是定义函数、应用中性, Agda **无法从 `?m + ?n ≡ e` 反分解出 m/n** ⇒ 元变量不化。
--   修法: **参数一律显式给**（`plus-zero-split (g fzero) (…) p`）。判据可推广:
--   **给非单射的定义函数传 `_` = 自埋元变量**; Fin 侧 `fzero`/`fsuc`、ℕ 侧 `zero`/`suc`
--   亦已全文核对（流水 235）。
--
-- 依赖: NSEFixedPointStrict（isNonZero/fold1N/countOver/supportCount）;
--       NSEFixedPoint（comp）; NSEOnT6 / Base.Trit

module Sovereign.Problem.NavierStokes.NSESupportZero where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂)
open import Sovereign.Problem.NavierStokes.NSEOnT6 using
  (C3; Torus6; ScalarField; Field; v1; v2; v3; v4; v5; v6)
open import Sovereign.Problem.NavierStokes.NSEFixedPoint using (comp)
open import Sovereign.Problem.NavierStokes.NSEFixedPointStrict using
  (isNonZero; fold1N; countOver; supportCount)

--------------------------------------------------------------------------------
-- §1. ℕ 加法归零拆分（自备; **参数一律显式**）
--------------------------------------------------------------------------------

plus-zero-split : ∀ m n → m + n ≡ zero → (m ≡ zero) × (n ≡ zero)
plus-zero-split zero    n p = refl , p
plus-zero-split (suc m) n ()

--------------------------------------------------------------------------------
-- §2. 归零提取（→ 方向的零件）
--------------------------------------------------------------------------------

isNonZero-zero : ∀ t → isNonZero t ≡ zero → t ≡ T₀
isNonZero-zero T₀ p = refl
isNonZero-zero T₁ ()
isNonZero-zero T₂ ()

fold1N-zero : ∀ (g : C3 → ℕ) → fold1N g ≡ zero → ∀ y → g y ≡ zero
fold1N-zero g p fzero =
  proj₁ (plus-zero-split (g fzero) (g (fsuc fzero) + g (fsuc (fsuc fzero))) p)
fold1N-zero g p (fsuc fzero) =
  proj₁ (plus-zero-split (g (fsuc fzero)) (g (fsuc (fsuc fzero)))
    (proj₂ (plus-zero-split (g fzero) (g (fsuc fzero) + g (fsuc (fsuc fzero))) p)))
fold1N-zero g p (fsuc (fsuc fzero)) =
  proj₂ (plus-zero-split (g (fsuc fzero)) (g (fsuc (fsuc fzero)))
    (proj₂ (plus-zero-split (g fzero) (g (fsuc fzero) + g (fsuc (fsuc fzero))) p)))

countOver-zero : ∀ (f : ScalarField) x1 x2 x3 x4 x5 x6 →
  countOver f ≡ zero → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)) ≡ zero
countOver-zero f x1 x2 x3 x4 x5 x6 p =
  fold1N-zero (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))
    (fold1N-zero (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))
      (fold1N-zero (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))
        (fold1N-zero (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))))
          (fold1N-zero (λ x2 → fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))))
            (fold1N-zero (λ x1 → fold1N (λ x2 → fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))))) p x1)
            x2) x3) x4) x5) x6

--------------------------------------------------------------------------------
-- §3. 逐点归零（← 方向的零件）
--------------------------------------------------------------------------------

isNonZero-T₀ : ∀ t → t ≡ T₀ → isNonZero t ≡ zero
isNonZero-T₀ t q = trans (cong isNonZero q) refl

fold1N-cong : ∀ {g g' : C3 → ℕ} → (∀ y → g y ≡ g' y) → fold1N g ≡ fold1N g'
fold1N-cong {g} {g'} p =
  trans (cong (λ z → z + (g (fsuc fzero) + g (fsuc (fsuc fzero)))) (p fzero))
  (trans (cong (λ z → g' fzero + (z + g (fsuc (fsuc fzero)))) (p (fsuc fzero)))
         (cong (λ z → g' fzero + (g' (fsuc fzero) + z)) (p (fsuc (fsuc fzero)))))

countOver-all-zero : ∀ (f : ScalarField) → (∀ x → f x ≡ T₀) → countOver f ≡ zero
countOver-all-zero f p = trans cz1 refl
  where
    -- 逐层具名（**签名钉死 g/g'**, 规避嵌套 λ 下隐式参数的模式合一失效）
    nz : ∀ x1 x2 x3 x4 x5 x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)) ≡ zero
    nz x1 x2 x3 x4 x5 x6 =
      isNonZero-T₀ (f (x1 , x2 , x3 , x4 , x5 , x6)) (p (x1 , x2 , x3 , x4 , x5 , x6))

    cz6 : ∀ x1 x2 x3 x4 x5 →
      fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))
      ≡ fold1N (λ _ → zero)
    cz6 x1 x2 x3 x4 x5 = fold1N-cong (λ x6 → nz x1 x2 x3 x4 x5 x6)

    cz5 : ∀ x1 x2 x3 x4 →
      fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))
      ≡ fold1N (λ _ → fold1N (λ _ → zero))
    cz5 x1 x2 x3 x4 = fold1N-cong (λ x5 → cz6 x1 x2 x3 x4 x5)

    cz4 : ∀ x1 x2 x3 →
      fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))
      ≡ fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → zero)))
    cz4 x1 x2 x3 = fold1N-cong (λ x4 → cz5 x1 x2 x3 x4)

    cz3 : ∀ x1 x2 →
      fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6))))))
      ≡ fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → zero))))
    cz3 x1 x2 = fold1N-cong (λ x3 → cz4 x1 x2 x3)

    cz2 : ∀ x1 →
      fold1N (λ x2 → fold1N (λ x3 → fold1N (λ x4 → fold1N (λ x5 → fold1N (λ x6 → isNonZero (f (x1 , x2 , x3 , x4 , x5 , x6)))))))
      ≡ fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → zero)))))
    cz2 x1 = fold1N-cong (λ x2 → cz3 x1 x2)

    cz1 : countOver f
        ≡ fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → fold1N (λ _ → zero))))))
    cz1 = fold1N-cong (λ x1 → cz2 x1)

-- 六项 ℕ 和的同余（J 一次给出; 调用点类型由 countOver-all-zero 钉死, 无元变量风险）
plus6-cong : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ e₁ e₂ f₁ f₂ : ℕ} →
  a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ → d₁ ≡ d₂ → e₁ ≡ e₂ → f₁ ≡ f₂ →
  (a₁ + (b₁ + (c₁ + (d₁ + (e₁ + f₁))))) ≡ (a₂ + (b₂ + (c₂ + (d₂ + (e₂ + f₂)))))
plus6-cong refl refl refl refl refl refl = refl

--------------------------------------------------------------------------------
-- §4. 主定理: supportCount v ≡ 0 ⇔ 逐点全零
--------------------------------------------------------------------------------

supportCount-zero→ : ∀ (v : Field) → supportCount v ≡ zero →
  ∀ k x → comp k v x ≡ T₀
supportCount-zero→ v p = cases
  where
    a1 = countOver (v1 v)
    a2 = countOver (v2 v)
    a3 = countOver (v3 v)
    a4 = countOver (v4 v)
    a5 = countOver (v5 v)
    a6 = countOver (v6 v)

    s1 = plus-zero-split a1 (a2 + (a3 + (a4 + (a5 + a6)))) p
    s2 = plus-zero-split a2 (a3 + (a4 + (a5 + a6))) (proj₂ s1)
    s3 = plus-zero-split a3 (a4 + (a5 + a6)) (proj₂ s2)
    s4 = plus-zero-split a4 (a5 + a6) (proj₂ s3)
    s5 = plus-zero-split a5 a6 (proj₂ s4)

    cases : ∀ k x → comp k v x ≡ T₀
    cases fzero (x1 , x2 , x3 , x4 , x5 , x6) =
      isNonZero-zero (v1 v (x1 , x2 , x3 , x4 , x5 , x6))
                     (countOver-zero (v1 v) x1 x2 x3 x4 x5 x6 (proj₁ s1))
    cases (fsuc fzero) (x1 , x2 , x3 , x4 , x5 , x6) =
      isNonZero-zero (v2 v (x1 , x2 , x3 , x4 , x5 , x6))
                     (countOver-zero (v2 v) x1 x2 x3 x4 x5 x6 (proj₁ s2))
    cases (fsuc (fsuc fzero)) (x1 , x2 , x3 , x4 , x5 , x6) =
      isNonZero-zero (v3 v (x1 , x2 , x3 , x4 , x5 , x6))
                     (countOver-zero (v3 v) x1 x2 x3 x4 x5 x6 (proj₁ s3))
    cases (fsuc (fsuc (fsuc fzero))) (x1 , x2 , x3 , x4 , x5 , x6) =
      isNonZero-zero (v4 v (x1 , x2 , x3 , x4 , x5 , x6))
                     (countOver-zero (v4 v) x1 x2 x3 x4 x5 x6 (proj₁ s4))
    cases (fsuc (fsuc (fsuc (fsuc fzero)))) (x1 , x2 , x3 , x4 , x5 , x6) =
      isNonZero-zero (v5 v (x1 , x2 , x3 , x4 , x5 , x6))
                     (countOver-zero (v5 v) x1 x2 x3 x4 x5 x6 (proj₁ s5))
    cases (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (x1 , x2 , x3 , x4 , x5 , x6) =
      isNonZero-zero (v6 v (x1 , x2 , x3 , x4 , x5 , x6))
                     (countOver-zero (v6 v) x1 x2 x3 x4 x5 x6 (proj₂ s5))

supportCount-zero← : ∀ (v : Field) → (∀ k x → comp k v x ≡ T₀) →
  supportCount v ≡ zero
supportCount-zero← v h =
  trans (plus6-cong
           (countOver-all-zero (v1 v) (λ x → h fzero x))
           (countOver-all-zero (v2 v) (λ x → h (fsuc fzero) x))
           (countOver-all-zero (v3 v) (λ x → h (fsuc (fsuc fzero)) x))
           (countOver-all-zero (v4 v) (λ x → h (fsuc (fsuc (fsuc fzero))) x))
           (countOver-all-zero (v5 v) (λ x → h (fsuc (fsuc (fsuc (fsuc fzero)))) x))
           (countOver-all-zero (v6 v) (λ x → h (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) x)))
        refl

--------------------------------------------------------------------------------
-- §5. 诚实边界
--
-- ✓ 已证: **supportCount v ≡ 0 ⇔ ∀ k x → comp k v x ≡ T₀**（零元端完整刻画）。
-- ✗ 不声称（⑤ 仍开放的部分）:
--   ① supportCount 在 `nsStep` 下的**单调性/非单调性**（集中度定理本体）;
--   ② supportCount 的**逐值分布**（正计数的原像刻画）;
--   ③ 「零元刻画 ⇒ 无集中」**不成立**;
--   ④ 连续统 NS 的任何结论。
--------------------------------------------------------------------------------
