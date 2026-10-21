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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; cons; _++w_; AStep; slide; expand)
open import Data.Product using (proj₂)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (ctarget; foldT; cEdge; foldT-++)
open import Sovereign.Synthesis.Homotopy.T6CayleyInterp
  using (interpAt; toStep; interpAt-++-glue)
open import Sovereign.Synthesis.Homotopy.T6AStepCode using (ADir; dslide; dexpand)
open import Sovereign.Synthesis.Homotopy.T6AStepMap
  using (srcCode; tgtCode; StepVertex; StepSide; StepVertex→StepSide; interpC-walk)
open import Sovereign.Synthesis.Homotopy.T6AStepCode2 using (StepCode; mkStep)

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
-- §3. ★★★ 补 `ASTep` 的另一半：`expand` 方向（`toStep` 只造 `slide`）
--
-- **本批发现的真实缺口**：`T6CayleyInterp.toStep` 的签名**不接收 `ADir`**
-- ⇒ 它只构造 `slide`，**从不构造 `expand`** ✗
-- 于是「码 → 步」只覆盖了 `ASTep` 的**一半**。
--
-- ⚠ 一个**不可行**的设计（本批实测否决）：想用 `d : ADir` **分派**到一个函数。
-- 但两个构造子的**结论方向相反**：
-- ```
--   slide  … : AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
--   expand … : AStep G (p ++w (cons e3 b)) (p ++w (cons e1 (cons e2 b)))
-- ```
-- ⇒ 单一（不依赖 `d` 的）结论类型**不可能**，必须拆成两个函数 ✗
-- （报错原文：`The terms cons {…s2} _ _ and cons {…s1} (cEdge … s1) _ are not equal`。）
--
-- ## 本模块交付：`expand` 侧（与 `toStep` 是镜像）
--
-- 同样**只吃顶点层侧条件**（`e3` 的对端由 `h` 对齐）✓
--------------------------------------------------------------------------------

toStepExpand :
  ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 s3 : CStep n) (suff : CWalk n)
  → (h : ctarget (foldT u pref) s3 ≡ ctarget (ctarget (foldT u pref) s1) s2)
  → AStep (T6CayleySym n)
          (interpAt u pref ++w
            (cons (subst (λ w → T6SymEdge (foldT u pref) w) h
                         (cEdge (foldT u pref) s3))
                  (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff)))
          (interpAt u pref ++w
            (cons (cEdge (foldT u pref) s1)
                  (cons (cEdge (ctarget (foldT u pref) s1) s2)
                        (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff))))
toStepExpand u pref s1 s2 s3 suff h =
  expand (interpAt u pref) (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff)
         (cEdge (foldT u pref) s1) (cEdge (ctarget (foldT u pref) s1) s2)
         (subst (λ w → T6SymEdge (foldT u pref) w) h (cEdge (foldT u pref) s3))

--------------------------------------------------------------------------------
-- §4. ★★ `ASTep` 沿**走等式**的铸型（两条一行 helper）
--
-- `astStep-cast`（协作者给的）只能沿**端点**等式铸型；
-- 要把 `toStep` 的走换成码层的走，需要沿**走本身**的等式铸型 ——
-- 而它对构造子同样是**一步 `refl`**（与 `subst-cons` / `slide-subst` 同族）✓
--------------------------------------------------------------------------------

astStep-src : ∀ {n : ℕ} {U V : T6Vec n} {p p' : Walk (T6CayleySym n) U V}
              {q : Walk (T6CayleySym n) U V}
            → p ≡ p' → AStep (T6CayleySym n) p q
            → AStep (T6CayleySym n) p' q
astStep-src refl s = s

astStep-tgt : ∀ {n : ℕ} {U V : T6Vec n} {q q' : Walk (T6CayleySym n) U V}
              {p : Walk (T6CayleySym n) U V}
            → q ≡ q' → AStep (T6CayleySym n) p q
            → AStep (T6CayleySym n) p q'
astStep-tgt refl s = s

--------------------------------------------------------------------------------
-- §5. ⚠ `toStepCode` —— **本批未完成，卡点已定位到「结构性」而非「工作量」**
--
-- ## 精确的桥（已核对 `T6AStepMap` 真实签名，不是猜）
--
-- ```
--   interpC-walk  u w : subst (Walk G u) (interpC-end u w) (proj₂ (interpC u w)) ≡ interpAt u w
--   interpC-walk' u w : proj₂ (interpC u w) ≡ subst (Walk G u) (sym (interpC-end u w)) (interpAt u w)
--   srcCode-glue      : interpAt u (srcCode c) ≡ subst (Walk G u) (sym (foldT-++ …)) (源 ++w 形态)
-- ```
--
-- ## ★ 结构性卡点（本批新发现，比「5–6 条交换引理」更精确）
--
-- `toStep` 给出的两步的**端点不同**：
-- ```
--   源：foldT u (srcCode c)                      = foldT u (pref ++ (s1∷s2∷suff))
--   靶：foldT (ctarget (ctarget (foldT u pref) s1) s2) suff
-- ```
-- ⇒ 要把两侧都搬到码层，需要**两个不同的**端点等式：
-- ```
--   eS : foldT (ctarget (ctarget (foldT u pref) s1) s2) suff ≡ foldT u (pref ++ (s1∷s2∷suff))
--   eT : foldT (ctarget (foldT u pref) s3) suff          ≡ foldT u (pref ++ (s3∷suff))
-- ```
-- 而 **`astStep-cast`（协作者给的）只用同一个 `e` 铸两侧**（因为 `ASTep G p q` 要求
-- `p`、`q` **端点相同**）⇒ 一侧一铸会在**中间态**产生 `ASTep` 端点不匹配 ⇒ 类型不成立 ✗
--
-- **⇒ 需要的是「联合铸型」**：一次用 `subst₂`/`cong₂` 同时改两侧的端点，
--   而不是两次单侧铸型。这不是「多写几条引理」，是**换铸型的方式**。
--
-- ## 已交的零件（本模块内已证 ✓）
--
-- | 件 | 内容 |
-- |---|---|
-- | `astStep-src` | 沿**走**等式铸源侧（一行，`refl` 级）|
-- | `astStep-tgt` | 沿**走**等式铸靶侧（一行，`refl` 级）|
--
-- ## 下一步（若继续做）
--
-- 写 `astStep-cast₂ : (eS : V₁ ≡ V₁') (eT : V₂ ≡ V₂') → AStep G p q
--                   → AStep G (subst … eS p) (subst … eT q)` ——
-- 它**能**成立（两侧同改后端点仍相同，因为 `eS`/`eT` 由 `StepSide` 对齐），
-- 且同样是 `refl` 级。**本批未写**（闸门已触发 9 次，按 §5.9 停手）。
--------------------------------------------------------------------------------
