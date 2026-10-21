{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyNormEnd
--
-- **闭合 `T6CayleyNorm` §「④ 语义正确 ⋯ **未证**」**：归约**不改变** `foldT` 终点
--
-- ## 陈述
--
-- ```
--   creduceA-fold : foldT x (creduceA w) ≡ foldT x w
-- ```
--
-- `creduceA = cpassA []` 是栈式单遍归约（`T6CayleyNorm` §1）。
-- 此前已知的只有 `T6CayleyCheck.check-end`：**一个具体词**上终点不变（`refl`）。
-- 本模块给出**全称**版本。
--
-- ## 证法：把栈的语义显式化
--
-- 栈 `acc` 存的是「已处理前缀」的**反向** ⇒ 关键不变量
-- ```
--   cpassA-fold : foldT x (cpassA acc xs) ≡ foldT (FoldStack x acc) xs
-- ```
-- 其中 `FoldStack x acc = foldT x (reverse acc)` 是栈的语义值。
-- 三条子句：
--   · `xs = []`：`cpassA acc [] = reverse acc`，两边同归约 ✓；
--   · `acc = []`：定义性 ✓（`FoldStack x [s]` 与 `ctarget (FoldStack x []) s` 同值）；
--   · `acc = y ∷ acc'`：分 `DecEq-CStep s (cstep-inv y)` 两支
--     — `yes`：消去互逆对 ⇒ `ctarget-inv`（`ctarget (ctarget v y) (cstep-inv y) ≡ v`，三步归零的另一面）；
--     — `no`：压栈 ⇒ `unfold-reverse` + `foldT-++`。
--
-- ## ⚠ 两个技术要点（踩过的坑，别重犯）
--
-- 1. **`reverse` 只在一侧展开**会毁掉 conversion：`reverse = foldl (flip _∷_) []`，
--    若同一等式里一处写成 `foldT x (reverse acc)`、另一处已展开成 `foldl …`，Agda 判不等。
--    ⇒ 用**具名**语义值 `FoldStack`，两侧都经同一符号 ✓。
-- 2. `≡-Reasoning` 要用 `using (module ≡-Reasoning)` 才能 `open`（只写 `≡-Reasoning` 拿不到模块名）。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical；不重写 `T6CayleyNorm` 的任何件
--   · 本模块**不改** `T6CayleyNorm.agda`（协作者在改那块），只在旁侧补定理

module Sovereign.Synthesis.Homotopy.T6CayleyNormEnd where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; reverse; [_]; _++_)
open import Data.List.Properties using (unfold-reverse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (yes; no)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cstep-inv; DecEq-CStep)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (foldT; ctarget; foldT-++; ctarget-inv)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm using (cpassA; creduceA)

--------------------------------------------------------------------------------
-- §1. 栈的语义值（具名定义 —— 见头部「技术要点 1」）
--------------------------------------------------------------------------------

FoldStack : ∀ {n : ℕ} (x : T6Vec n) (acc : CWalk n) → T6Vec n
FoldStack x acc = foldT x (reverse acc)

-- 压一个元素到栈顶 = 在语义端走一步
FoldStack-∷ : ∀ {n : ℕ} (x : T6Vec n) (y : CStep n) (acc : CWalk n)
            → FoldStack x (y ∷ acc) ≡ ctarget (FoldStack x acc) y
FoldStack-∷ x y acc =
  trans (cong (foldT x) (unfold-reverse y acc)) (foldT-++ x (reverse acc) [ y ])

--------------------------------------------------------------------------------
-- §2. 两条分支桥（`yes`：消去互逆对；`no`：压栈）
--------------------------------------------------------------------------------

cancel-bridge : ∀ {n : ℕ} (x : T6Vec n) (y : CStep n) (acc : CWalk n)
                (s : CStep n) (p : s ≡ cstep-inv y) (xs : CWalk n)
              → foldT (FoldStack x (y ∷ acc)) (s ∷ xs)
                ≡ foldT (FoldStack x acc) xs
cancel-bridge x y acc s p xs = begin
  foldT (FoldStack x (y ∷ acc)) (s ∷ xs)
    ≡⟨ cong (λ w → foldT w (s ∷ xs)) (FoldStack-∷ x y acc) ⟩
  foldT (ctarget (FoldStack x acc) y) (s ∷ xs)
    ≡⟨ refl ⟩
  foldT (ctarget (ctarget (FoldStack x acc) y) s) xs
    ≡⟨ cong (λ s' → foldT (ctarget (ctarget (FoldStack x acc) y) s') xs) p ⟩
  foldT (ctarget (ctarget (FoldStack x acc) y) (cstep-inv y)) xs
    ≡⟨ cong (λ w → foldT w xs) (ctarget-inv (FoldStack x acc) y) ⟩
  foldT (FoldStack x acc) xs ∎

push-bridge : ∀ {n : ℕ} (x : T6Vec n) (s y : CStep n) (acc xs : CWalk n)
            → foldT (FoldStack x (s ∷ y ∷ acc)) xs
              ≡ foldT (FoldStack x (y ∷ acc)) (s ∷ xs)
push-bridge x s y acc xs = begin
  foldT (FoldStack x (s ∷ y ∷ acc)) xs
    ≡⟨ cong (λ w → foldT w xs) (FoldStack-∷ x s (y ∷ acc)) ⟩
  foldT (ctarget (FoldStack x (y ∷ acc)) s) xs
    ≡⟨ refl ⟩
  foldT (FoldStack x (y ∷ acc)) (s ∷ xs) ∎

--------------------------------------------------------------------------------
-- §3. ★ 核心不变量与主定理
--------------------------------------------------------------------------------

cpassA-fold : ∀ {n : ℕ} (x : T6Vec n) (acc xs : CWalk n)
            → foldT x (cpassA acc xs) ≡ foldT (FoldStack x acc) xs
cpassA-fold x acc []      = refl
cpassA-fold x [] (s ∷ xs) = cpassA-fold x [ s ] xs
cpassA-fold x (y ∷ acc) (s ∷ xs) with DecEq-CStep s (cstep-inv y)
... | yes p = trans (cpassA-fold x acc xs) (sym (cancel-bridge x y acc s p xs))
... | no  ¬p = trans (cpassA-fold x (s ∷ y ∷ acc) xs) (push-bridge x s y acc xs)

-- ★ 主定理：归约不改终点（全称版；此前只有 `T6CayleyCheck.check-end` 的具体点版）
creduceA-fold : ∀ {n : ℕ} (x : T6Vec n) (w : CWalk n)
              → foldT x (creduceA w) ≡ foldT x w
creduceA-fold x w = cpassA-fold x [] w

--------------------------------------------------------------------------------
-- §4. 对抗验证：在 `T6CayleyCheck` 已用过的具体点上与既有 `refl` 对照
--
-- `check-end` 只对 `ep ∷ em ∷ []` 说过「终点不变」；这里同一词由**全称定理**给出，
-- 两条路径必须一致 —— 一致性由内核在 `T6CayleyCheck` 内已有 `refl` 见证间接保证，
-- 本模块不重复造具体点（避免与协作者的 `T6CayleyCheck` 重复实现）。
--------------------------------------------------------------------------------