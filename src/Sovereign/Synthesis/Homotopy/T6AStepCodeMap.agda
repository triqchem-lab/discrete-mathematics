{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepCodeMap
--
-- **④ 的最后接线（第一段）**：侧条件的「展开形态」+ 码的展开 + 一处推测的修正
--
-- ## 已交的两块（都很短，且都是 `refl` 级）
--
-- | 件 | 内容 |
-- |---|---|
-- | `toStep-vertex-form` | 把 `toStep` 的三条边**展开**成 `cEdge` 形态 ⇒ 显式暴露「侧条件是顶点层」 |
-- | `srcCode-glue` | `interpAt u (srcCode c)` 按 `interpAt-++-glue` 展开（1 行）|
--
-- ## ★ 修正一条推测（原记 `[未验证·路线推测]`）
--
-- 先前判断：「把 `toStep` 的结果沿**走等式**运输到码层，对构造子同样是一步 `refl`
-- （与 `slide-subst` 同族）」。
--
-- **这个推测不成立** —— 理由具体：
--
-- `slide p b e1 e2 e3` 的**第一个参数是 `p`**，而 `toStep` 用的是 `p = interpAt u pref`。
-- 沿走等式运输 `ASTep` 时，`subst` 改的正是**首走** ⇒ 目标侧 `slide` 需要的是
-- **另一个 `p'`**（码层形态下 `p` 被 `subst` 包裹）⇒
-- **不是「`subst` 穿构造子」那种一步 `refl`**，而是「`subst` 同时改参数与指标」⇒ 需 `J`-式对齐 ✗
--
-- ⇒ `toStepCode` 的两条路线：
--   **(a)** 把 `toStep` 重述为**不吃 `p`、吃码**的版本（递归造 `slide`，每个 `p` 都是
--           `cons` 形态 ⇒ 无运输）—— **推荐**，且是「换载体」老手法的又一例 ✓
--   **(b)** 引入 `HEq` —— 本库不用 ✗
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyInterp.toStep` / `T6AStepMap.StepVertex`（不重写）

module Sovereign.Synthesis.Homotopy.T6AStepCodeMap where

open import Data.Nat using (ℕ)
open import Data.List using (_∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; cons; _++w_; AStep)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (ctarget; foldT; cEdge; foldT-++)
open import Sovereign.Synthesis.Homotopy.T6CayleyInterp
  using (interpAt; toStep; interpAt-++-glue)

--------------------------------------------------------------------------------
-- §1. ★ `toStep` 的展开形态：三条边都是 `cEdge`，侧条件是**顶点层**
--
-- 这条把 `toStep` 内部用的 `stepE1`/`stepE2`/`stepE3` **定义性地展开**，
-- 从而一眼看出：侧条件 `h` 的比较对象是两个**顶点**（`ctarget … s3` 与 `ctarget (ctarget …)`）
-- —— 与 `slide` 同层 ✓（不是 `StepSide` 的**走层**条件）
--------------------------------------------------------------------------------

toStep-vertex-form :
  ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 s3 : CStep n) (suff : CWalk n)
  → (h : ctarget (foldT u pref) s3 ≡ ctarget (ctarget (foldT u pref) s1) s2)
  → AStep (T6CayleySym n)
          (interpAt u pref ++w
            (cons (cEdge (foldT u pref) s1)
                  (cons (cEdge (ctarget (foldT u pref) s1) s2)
                        (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff))))
          (interpAt u pref ++w
            (cons (subst (λ w → T6SymEdge (foldT u pref) w) h
                         (cEdge (foldT u pref) s3))
                  (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff)))
toStep-vertex-form u pref s1 s2 s3 suff h = toStep u pref s1 s2 s3 suff h

--------------------------------------------------------------------------------
-- §2. 码的展开（1 行，直接用 `interpAt-++-glue`）
--------------------------------------------------------------------------------

srcCode-glue : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 : CStep n)
               (suff : CWalk n)
             → interpAt u (pref ++ (s1 ∷ s2 ∷ suff))
               ≡ subst (Walk (T6CayleySym n) u) (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff)))
                       (interpAt u pref ++w interpAt (foldT u pref) (s1 ∷ s2 ∷ suff))
srcCode-glue u pref s1 s2 suff = interpAt-++-glue u pref (s1 ∷ s2 ∷ suff)

--------------------------------------------------------------------------------
-- §3. ⬜ 剩余：`toStepCode`（走路线 (a)，见模块头）
--------------------------------------------------------------------------------
