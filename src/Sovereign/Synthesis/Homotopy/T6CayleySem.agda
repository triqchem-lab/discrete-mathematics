{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleySem
--
-- **③ 语义正确**：归约不改变走的终点
--
-- ## 陈述
--
-- ```
--   cpassS-fold : foldStack x (cpassS acc xs) ≡ foldT (foldStack x acc) xs
-- ```
-- 读法：**先把栈 `acc` 读完，再读 `xs`** —— 与「先读完 `xs` 得到新栈、再读新栈」一致。
--
-- ⇒ 取 `acc = []`、`x = 起点`：`foldStack x (creduceS w) ≡ foldT x w`
--   —— **归约保持终点** ✓
--
-- ## 为什么能避开 `reverse`
--
-- `cpassS` 的栈是「最新在前」，所以栈的语义是**右折叠**（末尾的元素先应用）：
-- ```
--   foldStack x []        = x
--   foldStack x (s ∷ acc) = ctarget (foldStack x acc) s
-- ```
-- 它直接按栈的结构递归，**不需要** `reverse` ✓
-- （对比 `foldT` 是左折叠，用于**阅读序**的码走。）
--
-- ## 为什么只靠 `ctarget-inv` 就够了
--
-- `yes` 分支（消去一对）需要：走 `y` 再走 `x₀ = cstep-inv y` 回到原点 ——
-- 这正是 **`ctarget-inv`**（← `updAt-cubed`，特征 3）✓
-- 全部证明只用它 + 定义性展开，**没有任何新的数学输入**。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCodeWalk` 的 `ctarget` / `ctarget-inv` / `foldT`（不重写）

module Sovereign.Synthesis.Homotopy.T6CayleySem where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; reverse; _++_; _∷ʳ_)
open import Data.List.Properties using (unfold-reverse; ∷ʳ-++; ++-identityʳ)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; trans; subst; module ≡-Reasoning)
open ≡-Reasoning

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cstep-inv; DecEq-CStep)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk
  using (ctarget; ctarget-inv; foldT; foldT-++)
open import Sovereign.Synthesis.Homotopy.T6CayleyNorm
  using (cpassS; creduceS)

--------------------------------------------------------------------------------
-- §1. 栈的语义：**右折叠**（末尾元素先应用）
--------------------------------------------------------------------------------

foldStack : ∀ {n : ℕ} (x : T6Vec n) → CWalk n → T6Vec n
foldStack x []        = x
foldStack x (s ∷ acc) = ctarget (foldStack x acc) s

--------------------------------------------------------------------------------
-- §2. ★★★ 主定理：`cpassS` 保持「栈语义 + 阅读序」的组合
--------------------------------------------------------------------------------

cpassS-fold : ∀ {n : ℕ} (x : T6Vec n) (acc xs : CWalk n)
            → foldStack x (cpassS acc xs) ≡ foldT (foldStack x acc) xs
cpassS-fold x acc [] = refl
cpassS-fold x [] (s ∷ xs) = cpassS-fold x (s ∷ []) xs
cpassS-fold x (y ∷ acc') (s ∷ xs) with DecEq-CStep s (cstep-inv y)
-- 消去一对：`y` 之后走 `s = cstep-inv y` 回到原点（`ctarget-inv`）
... | yes p =
  trans (cpassS-fold x acc' xs)
        (trans (sym (cong (λ z → foldT z xs)
                          (ctarget-inv (foldStack x acc') y)))
               (sym (cong (λ z → foldT (ctarget (ctarget (foldStack x acc') y) z) xs)
                          p)))
-- 不消：两边同构
... | no  _ = cpassS-fold x (s ∷ y ∷ acc') xs

--------------------------------------------------------------------------------
-- §3. ★★ 推论：归约保持终点
--------------------------------------------------------------------------------

creduceS-fold : ∀ {n : ℕ} (x : T6Vec n) (w : CWalk n)
              → foldStack x (creduceS w) ≡ foldT x w
creduceS-fold x w = cpassS-fold x [] w

--------------------------------------------------------------------------------
-- §4. ⚠ 本模块**不**声称的
--
-- · ✅ **已证**（本模块 §7 `foldStack-foldT`）：`foldStack x acc ≡ foldT x (reverse acc)`
--   （栈语义与阅读序的桥；需要 stdlib 的 `unfold-reverse` + `∷ʳ-++` + `++-identityʳ`）
--   （需要 `reverse` 的性质；本模块的陈述不需要它）
-- · ✅ **已证（在别处）**：对 `creduceA`（含末尾 `reverse`）的对应陈述 =
--   **`T6CayleyNormEnd.creduceA-fold`**（全称版，回执 0679c767）—— 不在本模块。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §7. ★ 栈语义与阅读序的桥（§6 自标「未证」的那条）
--
-- `foldStack` 从**尾部**往头累积，`foldT` 从**头部**往后推进 —— 两者差的正是 `reverse`。
--------------------------------------------------------------------------------

foldStack-foldT : ∀ {n : ℕ} (x : T6Vec n) (acc : CWalk n)
                → foldStack x acc ≡ foldT x (reverse acc)
foldStack-foldT x [] = refl
foldStack-foldT x (s ∷ acc) =
  begin
    foldStack x (s ∷ acc)
  ≡⟨ cong (λ v → ctarget v s) (foldStack-foldT x acc) ⟩
    ctarget (foldT x (reverse acc)) s
  ≡⟨ refl ⟩
    foldT (foldT x (reverse acc)) (s ∷ [])
  ≡⟨ sym (foldT-++ x (reverse acc) (s ∷ [])) ⟩
    foldT x (reverse acc ++ (s ∷ []))
  ≡⟨ cong (foldT x) (begin
        reverse acc ++ (s ∷ [])
      ≡⟨ sym (∷ʳ-++ (reverse acc) s []) ⟩
        (reverse acc ∷ʳ s) ++ []
      ≡⟨ ++-identityʳ (reverse acc ∷ʳ s) ⟩
        reverse acc ∷ʳ s
      ≡⟨ sym (unfold-reverse s acc) ⟩
        reverse (s ∷ acc) ∎) ⟩
    foldT x (reverse (s ∷ acc))
  ∎

