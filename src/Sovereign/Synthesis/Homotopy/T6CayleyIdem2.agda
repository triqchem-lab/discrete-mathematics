{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyIdem2
--
-- **② 幂等（实施修法）**：追加版归约器 + 桥引理 + 主引理
--
-- ## 修法（台账 `PN.B4.creduce-idem-obstacle` 已写明）
--
-- 障碍：`reverse (x ∷ xs) = reverse xs ++ [x]` 把 `x` 推到**末尾**，
-- 而 `cpassB` 是**从头部**递归的 ⇒ 归纳假设用不上。
--
-- ⇒ 另起**追加版**（递归在尾部展开，与 `reverse xs ++ [x]` 同向）：
-- ```
--   pushB acc x            把 x 压到栈 acc 上（必要时消去）
--   cpassApp xs acc        从 xs 的**尾**往 acc 里压
-- ```
--
-- ## 为什么这一版能过（关键）
--
-- 需要「`¬ (x ≡ cstep-inv y)` ⇒ `pushB` 不消去」——而这**不需要反射引理**：
--
-- ```
--   ... with cdEqB x y in eq
--   ... | true  = ⊥-elim (¬p (cdEqB-sound x y (subst (λ b → T b) (sym eq) tt)))    -- 用 sound 造出矛盾
--   ... | false = refl
-- ```
--
-- ⇒ `cdEqB-sound`（已证，回执 `5e5aca53`）足够把 `true` 分支排空 ✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyBool` 的 `cpassB`/`cdEqB`/`cdEqB-sound` 与 `T6CayleyNorm` 的 `NoCancel`/`NoCancel-tail`

module Sovereign.Synthesis.Homotopy.T6CayleyIdem2 where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; reverse; _++_)
open import Data.List.Properties using (reverse-++)
open import Data.Bool using (Bool; true; false; T)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cstep-inv)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm
  using (NoCancel; nc-nil; nc-one; nc-two; NoCancel-tail)
open import Sovereign.Synthesis.Homotopy.T6CayleyBool
  using (cpassB; creduceB; cdEqB; cdEqB-sound; creduceB-noCancel)

--------------------------------------------------------------------------------
-- §1. `pushB`：把一步压到栈上（必要时消去）
--------------------------------------------------------------------------------

pushB : ∀ {n : ℕ} (acc : CWalk n) (x : CStep n) → CWalk n
pushB []        x = x ∷ []
pushB (y ∷ acc') x with cdEqB x y
... | true  = acc'
... | false = x ∷ y ∷ acc'

-- ★ 有 `¬` 前提时压栈不消去（`cdEqB-sound` 排空 `true` 分支）
pushB-no-cancel : ∀ {n : ℕ} (y : CStep n) (acc' : CWalk n) (x : CStep n)
                → ¬ (x ≡ cstep-inv y) → pushB (y ∷ acc') x ≡ x ∷ y ∷ acc'
pushB-no-cancel y acc' x ¬p with cdEqB x y in eq
... | true  = ⊥-elim (¬p (cdEqB-sound x y (subst (λ b → T b) (sym eq) tt)))
... | false = refl

--------------------------------------------------------------------------------
-- §2. 追加版：递归在**尾部**展开
--------------------------------------------------------------------------------

cpassApp : ∀ {n : ℕ} (xs : CWalk n) (acc : CWalk n) → CWalk n
cpassApp []       acc = acc
cpassApp (x ∷ xs) acc = cpassApp xs (pushB acc x)

--------------------------------------------------------------------------------
-- §3. ★★ 桥引理：`cpassB` 与 `cpassApp` 是同一函数
--------------------------------------------------------------------------------

cpassB≡cpassApp : ∀ {n : ℕ} (acc xs : CWalk n)
                → cpassB acc xs ≡ cpassApp xs acc
cpassB≡cpassApp acc [] = refl
cpassB≡cpassApp [] (x ∷ xs) = cpassB≡cpassApp (x ∷ []) xs
cpassB≡cpassApp (y ∷ acc') (x ∷ xs) with cdEqB x y in eq
... | true  = cpassB≡cpassApp acc' xs
... | false = cpassB≡cpassApp (x ∷ y ∷ acc') xs

--------------------------------------------------------------------------------
-- §4. 追加版对 `++` 的结合性
--------------------------------------------------------------------------------

cpassApp-++ : ∀ {n : ℕ} (a b : CWalk n) (acc : CWalk n)
            → cpassApp (a ++ b) acc ≡ cpassApp b (cpassApp a acc)
cpassApp-++ []       b acc = refl
cpassApp-++ (x ∷ a) b acc = cpassApp-++ a b (pushB acc x)

--------------------------------------------------------------------------------
-- §5. `reverse` 的单元素展开
--------------------------------------------------------------------------------

reverse-∷ : ∀ {n : ℕ} (x : CStep n) (xs : CWalk n)
          → reverse (x ∷ xs) ≡ reverse xs ++ (x ∷ [])
reverse-∷ x xs = reverse-++ (x ∷ []) xs

--------------------------------------------------------------------------------
-- §6. ★★★ 主引理：已归约的栈反向处理回来还是它
--------------------------------------------------------------------------------

-- 尾：`NoCancel (x ∷ xs)` ⇒ `NoCancel xs`
NoCancel-tail' : ∀ {n : ℕ} (x : CStep n) (xs : CWalk n)
               → NoCancel (x ∷ xs) → NoCancel xs
NoCancel-tail' x []       _        = nc-nil
NoCancel-tail' x (y ∷ xs) (nc-two .x y xs _ t) = t

-- 压栈不变：`NoCancel (x ∷ xs)` ⇒ `pushB xs x ≡ x ∷ xs`
pushB-eq : ∀ {n : ℕ} (x : CStep n) (xs : CWalk n)
         → NoCancel (x ∷ xs) → pushB xs x ≡ x ∷ xs
pushB-eq x []       _            = refl
pushB-eq x (y ∷ xs) (nc-two .x y .xs ¬p _) = pushB-no-cancel y xs x ¬p

cpassApp-rev : ∀ {n : ℕ} (v : CWalk n)
             → NoCancel v → cpassApp (reverse v) [] ≡ v
cpassApp-rev []       _ = refl
cpassApp-rev (x ∷ xs) h =
  trans (cong (λ z → cpassApp z []) (reverse-∷ x xs))
        (trans (cpassApp-++ (reverse xs) (x ∷ []) [])
               (trans (cong (λ z → cpassApp (x ∷ []) z)
                            (cpassApp-rev xs (NoCancel-tail' x xs h)))
                      (pushB-eq x xs h)))

-- ★★ 桥到 `cpassB`：`cpassB [] (reverse v) ≡ v`
cpassB-self : ∀ {n : ℕ} (v : CWalk n)
            → NoCancel v → cpassB [] (reverse v) ≡ v
cpassB-self v h = trans (cpassB≡cpassApp [] (reverse v)) (cpassApp-rev v h)

--------------------------------------------------------------------------------
-- §7. ★★★ ② 幂等（由 §6 直接推出）
--
-- `cpassB-self` 说：**已归约的栈**反向处理回来还是它。
-- 而 `cpassB [] w` 已被证是归约的（`creduceB-noCancel`）
-- ⇒ 再归约一次什么也不改 ✓
--------------------------------------------------------------------------------

creduceB-idem : ∀ {n : ℕ} (w : CWalk n)
              → cpassB [] (reverse (cpassB [] w)) ≡ cpassB [] w
creduceB-idem w = cpassB-self (cpassB [] w) (creduceB-noCancel w)

-- ★★★ ② 的目标陈述（`creduceB' w = reverse ∘ creduceB`）
creduceB'-idem : ∀ {n : ℕ} (w : CWalk n)
               → reverse (cpassB [] (reverse (cpassB [] w)))
                 ≡ reverse (cpassB [] w)
creduceB'-idem w = cong reverse (creduceB-idem w)
