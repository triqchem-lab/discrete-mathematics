{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNormNC
--
-- **闭合 `T6CayleyNorm` §4 的两条「未证」：`NoCancel-reverse` 与 `creduceA` 的范式性（②）**
--
-- ## 背景
--
-- `T6CayleyNorm` §4 只证了**栈序**版本 `NoCancel (creduceS w)`（`creduceS = cpassS []`），
-- 并明写：
-- > **未证**：阅读顺序下的版本 `NoCancel (reverse (creduceS w))`（需 `NoCancel-reverse`）。
-- > ⚠ 实测：`NoCancel-reverse` 比预期难 —— `reverse` 与 `nc-two` 的**头序相反**。
--
-- 而台账 `PN.B4.creduce-normal` 声称已证 `NoCancel (creduceA w)` —— 该定理**当时不存在**。
-- 本模块把它补上（因此该台账声言此后为真）。
--
-- ## 证法要点（把「头序相反」这件事做干净）
--
-- 1. **不用 `reverse` 递推**（`reverse = foldl (flip _∷_) []`，`unfold-reverse` 会让
--    同一等式两侧一处展开、一处不展开 ⇒ conversion 失败）。改为自己的**右折叠**
--    `revApp ws acc := reverse ws ++ acc`，它对 `ws` **定义性递推** ✓；
--    `revApp-eq` 再把它与 `reverse ws ++ acc` 接上（只在最终一步用）。
-- 2. 广义不变量（缓冲区 `y ∷ acc` 显式带着「交界元素」`y`）：
--    ```
--      aux ws y acc : NoCancelR ws → NoCancel (y ∷ acc)
--                   → (∀ z zs → ws ≡ z ∷ zs → ¬ (z ≡ cstep-inv y))
--                   → NoCancel (revApp ws (y ∷ acc))
--    ```
--    交界条件正是 `NoCancelR` 的 `nr-two` 提供的那一条 ⇒ 两个分支都只做一次 `λ { refl → ¬q }`。
-- 3. 结论 `NoCancel (creduceA w)`：`cpassA-eq` + `creduceS-noCancelR` + `nc-reverse`。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · **不改** `T6CayleyNorm.agda`（旁侧模块补定理）

module Sovereign.Synthesis.Homotopy.T6CayleyNormNC where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; [_]; _++_; reverse)
open import Data.List.Properties using (unfold-reverse; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (¬_)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cstep-inv)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm using
  (NoCancel; nc-nil; nc-one; nc-two; NoCancel-tail; NoCancelR; nr-nil; nr-one; nr-two;
   cpassA; creduceA; cpassA-eq; creduceS; creduceS-noCancelR)

--------------------------------------------------------------------------------
-- §1. 右折叠 `revApp`（对 `ws` 定义性递推 —— 见头部要点 1）
--------------------------------------------------------------------------------

revApp : ∀ {n : ℕ} → CWalk n → CWalk n → CWalk n
revApp []       acc = acc
revApp (x ∷ xs) acc = revApp xs (x ∷ acc)

-- `++` 结合律（stdlib 的 `++-assoc` 名字随版本变动；此处直接用 `Data.List.Properties`）
++-assoc-list : ∀ {n : ℕ} (a b c : CWalk n) → (a ++ b) ++ c ≡ a ++ (b ++ c)
++-assoc-list []       b c = refl
++-assoc-list (x ∷ a)  b c = cong (x ∷_) (++-assoc-list a b c)

revApp-eq : ∀ {n : ℕ} (ws acc : CWalk n) → revApp ws acc ≡ reverse ws ++ acc
revApp-eq []       acc = refl
revApp-eq (x ∷ xs) acc = begin
  revApp xs (x ∷ acc)
    ≡⟨ revApp-eq xs (x ∷ acc) ⟩
  reverse xs ++ (x ∷ acc)
    ≡⟨ refl ⟩
  reverse xs ++ ([ x ] ++ acc)
    ≡⟨ sym (++-assoc-list (reverse xs) [ x ] acc) ⟩
  (reverse xs ++ [ x ]) ++ acc
    ≡⟨ cong (λ w → w ++ acc) (sym (unfold-reverse x xs)) ⟩
  reverse (x ∷ xs) ++ acc ∎

--------------------------------------------------------------------------------
-- §2. `NoCancelR` 的 tail 引理（与 `NoCancel-tail` 同形）
--------------------------------------------------------------------------------

NoCancelR-tail : ∀ {n : ℕ} (y : CStep n) (acc' : CWalk n)
               → NoCancelR (y ∷ acc') → NoCancelR acc'
NoCancelR-tail y []       (nr-one .y)          = nr-nil
NoCancelR-tail y (z ∷ zs) (nr-two .y z zs _ t) = t

--------------------------------------------------------------------------------
-- §3. ★★ 广义不变量：缓冲区带「交界元素」
--------------------------------------------------------------------------------

aux : ∀ {n : ℕ} (ws : CWalk n) (y : CStep n) (acc : CWalk n)
    → NoCancelR ws
    → NoCancel (y ∷ acc)
    → (∀ (z : CStep n) (zs : CWalk n) → ws ≡ z ∷ zs → ¬ (z ≡ cstep-inv y))
    → NoCancel (revApp ws (y ∷ acc))
aux []            y acc nr-nil           hy _ = hy
aux (x ∷ [])      y acc (nr-one .x)      hy j =
  nc-two x y acc (j x [] refl) hy
aux (x ∷ z ∷ zs)  y acc (nr-two .x z zs ¬q t) hy j =
  aux (z ∷ zs) x (y ∷ acc) t
      (nc-two x y acc (j x (z ∷ zs) refl) hy)
      (λ z' zs' → λ { refl → ¬q })

--------------------------------------------------------------------------------
-- §4. ★ `NoCancel-reverse`：阅读序版本的范式性
--------------------------------------------------------------------------------

nc-revApp : ∀ {n : ℕ} (w : CWalk n) → NoCancelR w → NoCancel (revApp w [])
nc-revApp []             nr-nil             = nc-nil
nc-revApp (x ∷ [])       (nr-one .x)        = nc-one x
nc-revApp (x ∷ y ∷ ys)   (nr-two .x y ys ¬q t) =
  aux (y ∷ ys) x [] t (nc-one x) (λ z' zs' → λ { refl → ¬q })

NoCancel-reverse : ∀ {n : ℕ} (w : CWalk n) → NoCancelR w → NoCancel (reverse w)
NoCancel-reverse w h =
  subst NoCancel (trans (revApp-eq w []) (++-identityʳ (reverse w)))
        (nc-revApp w h)

--------------------------------------------------------------------------------
-- §5. ★★ 主定理：`creduceA` 的输出不含相邻可消对（`T6CayleyNorm` ②）
--------------------------------------------------------------------------------

creduceA-noCancel : ∀ {n : ℕ} (w : CWalk n) → NoCancel (creduceA w)
creduceA-noCancel w =
  subst NoCancel (sym (cpassA-eq [] w))
        (NoCancel-reverse (creduceS w) (creduceS-noCancelR w))
