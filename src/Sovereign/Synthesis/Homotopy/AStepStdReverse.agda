{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.AStepStdReverse
--
-- **⑤ 一般的走层逆**：`p ++w rev p ⁓ nil`
--
-- ## 陈述
--
-- ```
--   rev-cancel : ∀ (p : Walk G u v) → AHomotopyStd G (p ++w rev p) (nil u)
-- ```
-- （`sym-edge` 作为假设：需要每条边可反向。）
--
-- ## 证明（对 `p` 归纳）
--
-- `p = cons e q` 时，`rev (cons e q) = rev q ++w cons (sym-edge e) (nil _)`，故
--
-- ```
--   (cons e q) ++w rev (cons e q)
--   = cons e (q ++w (rev q ++w e'))            -- 定义（e' = cons (sym-edge e) nil）
--   ≡ cons e ((q ++w rev q) ++w e')            -- ++w-assoc（一次 subst）
--   ⁓ cons e (nil _ ++w e') = cons e e'        -- prefix-cong + 归纳假设 + 右同余
--   ⁓ nil u                                     -- 一条 bt（= rev-cancel-one e）
-- ```
--
-- ⇒ 全程只需要 **一次 `++w-assoc` 运输** + `prefix-cong` + 右同余 + `rev-cancel-one`
--   —— 这正是台账里记的「归纳结构已推通，只是传输较多」。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `Pi1dMonoid.++w-assoc`、`AStepStdMonoid.AHStd-++w`、
--     `AStepStdGroup.prefix-cong`/`rev`/`rev-cancel-one`（全部不重写）

module Sovereign.Synthesis.Homotopy.AStepStdReverse where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy
  using (DiGraph; Walk; nil; cons; bt; _++w_)
open DiGraph using (V; edge)
open import Sovereign.Synthesis.Homotopy.Pi1dMonoid using (++w-assoc)
open import Sovereign.Synthesis.Homotopy.AStepStd
  using (AHomotopyStd; rfl; trn; gen)
open import Sovereign.Synthesis.Homotopy.AStepStdMonoid using (AHStd-++w)
open import Sovereign.Synthesis.Homotopy.AStepStdGroup
  using (rev; rev-cancel-one; prefix-cong; subst-AHStd)

module _ {G : DiGraph} (sym-edge : ∀ {x y : V G} → edge G x y → edge G y x) where

  rev-cancel : ∀ {u v : V G} (p : Walk G u v)
             → AHomotopyStd G (p ++w rev sym-edge p) (nil u)
  rev-cancel (nil v) = rfl (nil v)
  rev-cancel (cons {u} {a} e q) =
    subst-AHStd (sym step) refl
      (trn (prefix-cong e (AHStd-++w (cons (sym-edge e) (nil u)) (rev-cancel q)))
           (rev-cancel-one sym-edge e))
    where
      -- `(cons e q) ++w rev (cons e q)` 规约到 `cons e ((q ++w rev q) ++w e')`
      step : ((cons e q) ++w rev sym-edge (cons e q))
           ≡ cons e ((q ++w rev sym-edge q) ++w cons (sym-edge e) (nil u))
      step = cong (cons e)
                  (sym (++w-assoc q (rev sym-edge q) (cons (sym-edge e) (nil u))))
