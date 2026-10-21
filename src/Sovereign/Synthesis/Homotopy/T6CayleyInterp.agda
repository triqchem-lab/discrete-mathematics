{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyInterp
--
-- **表示层修正**：把「码 → 走」的终点改成**计算出来的参数**，而不是 `Σ` 的投影
--
-- ## 为什么原来的 `interpC` 不好用（上一批失败的原因）
--
-- `interpC : (u) (w) → Σ (λ v → Walk G u v)` 的终点是 `proj₁ (interpC u w)`
-- —— 这是 **`Σ` 的投影**（**stuck 项**），与 `foldT u w` 不可相互归约
-- ⇒ 任何以 `foldT` 形态陈述的引理都要显式 `subst` ✗
--
-- ## 修正：终点**作为参数的计算值**
--
-- ```
--   interpAt : (u : T6Vec n) (w : CWalk n) → Walk (T6CayleySym n) u (foldT u w)
-- ```
-- 终点写成 **`foldT u w`**（**可计算**，不是投影）⇒
--
-- | `interpAt` | 证 |
-- |---|---|
-- | `[]` | `nil u`（`: Walk G u (foldT u []) = Walk G u u` ✓ 定义性）|
-- | `s ∷ ws` | `cons (cEdge u s) (interpAt (ctarget u s) ws)` —— 端点 `foldT (ctarget u s) ws` = `foldT u (s ∷ ws)` **定义性** ✓ |
--
-- ## 收益
--
-- 拼接拆解 `interpAt-++` 两情形都只需 **`refl` / `cong`**，**不需要 `subst`** ✓✓
-- （这正是上一批想证却卡住的那条，卡点在于端点形状而非数学。）
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCodeWalk` 的 `cEdge`（见证 = `refl`）/ `foldT` / `ctarget`

module Sovereign.Synthesis.Homotopy.T6CayleyInterp where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk
  using (ctarget; foldT; cEdge)

--------------------------------------------------------------------------------
-- §0. ★★ 前置：`foldT` 的拼接律（**不是 defeq**，必须证）
--
-- ```
--   foldT u (a ++ b) ≡ foldT (foldT u a) b
-- ```
-- 这正是 `interpAt-++` 卡住的根因：两边 `Walk` 的**终点**差这条等式
-- ⇒ 必须显式 `subst`（经验库 `projection-stuck-let` 的误判防护已写明「需要 `subst`」）。
--------------------------------------------------------------------------------

foldT-++ : ∀ {n : ℕ} (u : T6Vec n) (a b : CWalk n)
         → foldT u (a ++ b) ≡ foldT (foldT u a) b
foldT-++ u []      b = refl
foldT-++ u (s ∷ a) b = foldT-++ (ctarget u s) a b

--------------------------------------------------------------------------------
-- §1. 码 → 走（终点 = `foldT u w`，**可计算**）
--------------------------------------------------------------------------------

interpAt : ∀ {n : ℕ} (u : T6Vec n) (w : CWalk n)
         → Walk (T6CayleySym n) u (foldT u w)
interpAt u []       = nil u
interpAt u (s ∷ ws) = cons (cEdge u s) (interpAt (ctarget u s) ws)

--------------------------------------------------------------------------------
-- §2. ⬜ 拼接拆解 —— **未完成（本批尝试已撤回）**
--
-- 想要的陈述（`subst` 放在**拼接位置**，这样 `cons` 情形能整体 `cong`）：
-- ```
--   interpAt u (a ++ b)
--     ≡ interpAt u a ++w subst (Walk G (foldT u a)) (foldT-++ u a b)
--                              (interpAt (foldT u a) b)
-- ```
-- ⚠ `[]` 情形报 `UnequalTerms: foldT u a 与 u 不相等` —— 即 `subst` 的**索引**
--   `foldT u (a ++ b)` 在 `a := []` 时没有按预期归约成 `foldT u b`。
--   **待查**（下一步第一件事）：`subst` 的 motive 里 `foldT u (a ++ b)` 是
--   `_++_`-卡住的（`a` 为变量时 `a ++ b` 不归约）⇒ 可能要把 `++` 也改成
--   可计算形态，或先对 `a` 做 `with` 细化再写。
--
-- 已备零件：**`foldT-++`（§0，本批已证）** —— 这正是缺的那条等式。
--------------------------------------------------------------------------------
