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
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
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
-- §1b. ★★ `subst` 与 `cons` 交换（**一行**：对 `eq` 模式匹配到 `refl` 时两边一起归约）
--------------------------------------------------------------------------------

subst-cons : ∀ {n : ℕ} {a b : T6Vec n} {w w' : T6Vec n}
             (e : T6SymEdge a b) (p : Walk (T6CayleySym n) b w) (eq : w ≡ w')
           → subst (Walk (T6CayleySym n) a) eq (cons e p)
             ≡ cons e (subst (Walk (T6CayleySym n) b) eq p)
subst-cons e p refl = refl

--------------------------------------------------------------------------------
-- §2. ⬜ 拼接拆解 `interpAt-++` —— **未完成（已尝试 3 次，全部同一报错，如实保留）**
--
-- 想要的陈述（`subst` 在**拼接位置**）：
-- ```
--   interpAt u (a ++ b)
--     ≡ interpAt u a ++w subst (Walk G (foldT u a)) (foldT-++ u a b)
--                              (interpAt (foldT u a) b)
-- ```
-- **三次尝试的同一报错**（逐字）：
-- ```
-- The terms foldT u a and u are not equal at type Vec (Fin 3) n
-- when checking that the expression foldT-++ u a b has type
--       foldT u (a ++ b) ≡ foldT u (a ++ b)
-- ```
-- ⇒ 报错说 `foldT-++ u a b` 的**期望类型退化成自反式**，而项里 `a` 仍是变量
--   —— 即 `subst` 的 motive 里的索引 `foldT u (a ++ b)` 在 `a := []` 时
--   **没有**按预期归约成 `foldT u b`。
--
-- **已排除的路线**（都试过，都同一报错）：
--   ① 陈述无 `subst`；② `subst` 放整式上；③ `subst` 放拼接位置（本文件 §2 原样）。
--
-- **下一步最可能的方向**（未验证）：
--   把 `_++_` 换成**可计算形态**（如先 `with` 细化 `a`，或自写带模式子句的 append
--   使 `[] ++ b` 与 `s ∷ a ++ b` 都在**类型层**归约）；
--   或改用「两端都写成 `foldT` 右结合形」的陈述以彻底避开 `subst`。
--
-- 已备零件：**`subst-cons`（§1b，一行）+ `foldT-++`（§0）+ `interpAt`（§1）** —— 三者都绿。
--------------------------------------------------------------------------------
