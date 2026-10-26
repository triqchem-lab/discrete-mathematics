{-# OPTIONS --cubical --guardedness #-}

-- | Sovereign.Synthesis.Representation.BraidQuotientCubical
-- **B₃ 作为商类型**：`B3 = Word / _≈b_`（cubical 集合商），连同其消除子与唯一性。
--
-- 为什么用 cubical HIT 而不是只留 setoid：
--   `BraidQuotientRec.resp` 只是 `SetQuotients.rec` 的**前提**（点式蕴含），
--   拿不到"商是一个类型"这件事。有了 `B3`，
--     · 下降成为 `B3-rec : (Word → X) → B3 → X`（**函数**，不是逐点命题）；
--     · 唯一性成为 `B3-uniq`：任何与 `[_]` 复合后相同的 `g` 与下降结果逐点相等。
--   这才是泛性质的**类型级**形态。
--
-- 为什么本件的导入锥是干净的：
--   只 import `Word`（零依赖语法层）与 `BraidCongruence`（只依赖 Word）。
--   两者都**不声明 `--rewriting`**，故本模块只开 `--cubical`。
--   这条很关键——探针实测：`--cubical` 下真正声明的 REWRITE 规则会被**静默忽略**
--   （`refl` 直接失败），所以 cubical 模块必须避开带真规则的导入锥。
--   全库带真规则的模块（T6 / XuanwuAbsorption / JacobianInjectiveSurjective / …）
--   都不在 B₃ 链上，本件也不导入它们。
--
-- 包含：B3 / B3-rec / B3-uniq
-- 0 postulate / 0 hole。

module Sovereign.Synthesis.Representation.BraidQuotientCubical where

open import Cubical.Foundations.Prelude using (Type; isSet; _≡_; refl)

open import Cubical.HITs.SetQuotients using (_/_; [_]; rec; elimProp)

open import Sovereign.Algebra.GroupTheory.Word using (Word)
open import Sovereign.Algebra.GroupTheory.BraidCongruence using (_≈b_)

--------------------------------------------------------------------------------
-- ① 商类型
--------------------------------------------------------------------------------

B3 : Type
B3 = Word / _≈b_

--------------------------------------------------------------------------------
-- ② 消除子：从「尊重同余的映射」得到「商的映射」
--------------------------------------------------------------------------------

B3-rec : ∀ {ℓ} {X : Type ℓ}
       → isSet X
       → (f : Word → X)
       → (∀ a b → a ≈b b → f a ≡ f b)
       → B3 → X
B3-rec sX f h = rec sX f h

--------------------------------------------------------------------------------
-- ③ 唯一性：与 `[_]` 复合后相同的映射必相同（逐点）
--
-- 因 X 是集合，`g x ≡ B3-rec … x` 是命题，可用 elimProp 沿商归纳。
--------------------------------------------------------------------------------

B3-uniq : ∀ {ℓ} {X : Type ℓ}
        → (sX : isSet X)
        → (f : Word → X)
        → (h : ∀ a b → a ≈b b → f a ≡ f b)
        → (g : B3 → X)
        → (∀ w → g [ w ] ≡ f w)
        → ∀ x → g x ≡ B3-rec sX f h x
B3-uniq sX f h g hg =
  elimProp (λ x → sX (g x) (B3-rec sX f h x)) (λ a → hg a)
