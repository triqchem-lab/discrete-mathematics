{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepMap
--
-- **④ 的映射骨架**：码 → 一步所关联的**两条走** + **侧条件**（可判定）
--
-- ## 为什么要拆成「数据 + 侧条件」
--
-- `slide` 的类型（`BarceloAHomotopy.agda:51-53`）：
-- ```
--   slide p b e1 e2 e3 : AStep G (p ++w (cons e1 (cons e2 b)))
--                              (p ++w (cons e3 b))
-- ```
-- ⇒ 一步所关联的**两条走**在码层完全确定：
--
-- | 量 | 码层 | 
-- |---|---|
-- | 源走 | `pref ++ (s1 ∷ s2 ∷ suff)` |
-- | 靶走 | `pref ++ (s3 ∷ suff)` |
-- | **侧条件** | 两者**终点相同**（否则 `e3` 的对端接不上）|
--
-- ⇒ 「码 → 步」的**内容**= 这两条走；而**何时成立**= 侧条件。
-- 本模块只交这两样 + 侧条件的**可判定性**；真正构造 `ASTep` 值留给下一步。
--
-- ## 侧条件为什么可判定
--
-- 两条走的终点都是 `T6Vec n` 的元素 ⇒ 用 `T6CayleyDec.DecEq-T6Vec` **可判定** ✓
-- （`Vec (Fin 3) n` 的相等可判定，不需要 `uip`。）
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCodeWalk.interpC`（码 → 走的终点）+ `T6CayleyDec.DecEq-T6Vec`

module Sovereign.Synthesis.Homotopy.T6AStepMap where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; _++_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (interpC; ctarget; foldT; cEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_)
open import Sovereign.Synthesis.Homotopy.T6AStepCode2 using (StepCode; mkStep)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym)
open import Sovereign.Synthesis.Homotopy.T6CayleyInterp using (interpAt; subst-cons)

--------------------------------------------------------------------------------
-- §1. 码层的两条走（`slide` / `expand` 共用同一对数据，只是方向相反）
--------------------------------------------------------------------------------

srcCode : ∀ {n : ℕ} → StepCode n → CWalk n
srcCode (mkStep _ pref s1 s2 _ suff) = pref ++ (s1 ∷ s2 ∷ suff)

tgtCode : ∀ {n : ℕ} → StepCode n → CWalk n
tgtCode (mkStep _ pref _ _ s3 suff) = pref ++ (s3 ∷ suff)

--------------------------------------------------------------------------------
-- §2. ★★ 侧条件：两条走的**终点相同**
--------------------------------------------------------------------------------

StepSide : ∀ {n : ℕ} (u : T6Vec n) → StepCode n → Set
StepSide u c = proj₁ (interpC u (srcCode c)) ≡ proj₁ (interpC u (tgtCode c))

-- ★ 侧条件**可判定**（不需要 uip）
decStepSide : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → Dec (StepSide u c)
decStepSide u c = DecEq-T6Vec (proj₁ (interpC u (srcCode c)))
                              (proj₁ (interpC u (tgtCode c)))

--------------------------------------------------------------------------------
-- §3. ★★ 关键前置：`interpC` 对拼接的分配律（端点层）
--
-- ```
--   proj₁ (interpC u (a ++ b)) ≡ proj₁ (interpC (proj₁ (interpC u a)) b)
-- ```
-- 对 `a` 归纳，**两情形都是定义性匹配** ✓（`[]` 情形 refl；`s ∷ a'` 情形交给 IH）。
--
-- ⚠ 这里只到**端点**层（`proj₁`）。走本身（`proj₂`）要对 `Walk` 做 `subst` 运输
--   —— 那一步留给真正构造 `ASTep` 时做。
--------------------------------------------------------------------------------

interpC-++ : ∀ {n : ℕ} (u : T6Vec n) (a b : CWalk n)
           → proj₁ (interpC u (a ++ b))
             ≡ proj₁ (interpC (proj₁ (interpC u a)) b)
interpC-++ u []       b = refl
interpC-++ u (s ∷ a)  b = interpC-++ (ctarget u s) a b

--------------------------------------------------------------------------------
-- §4. ★★★ `interpC` 的终点就是 `foldT`（端点层的「码 → 顶点」引理）
--
-- ```
--   proj₁ (interpC u w) ≡ foldT u w
-- ```
-- 对 `w` 归纳，**两情形都是 `refl`** ✓（`interpC` 与 `foldT` 的递归结构完全一致）。
--
-- ## 为什么这条关键
--
-- 侧条件 `StepSide u c` 说的是两个 `proj₁ (interpC …)` 相等；
-- 而真正要喂给 `slide` 的是 **`foldT` 形态的等式**（`ctarget` 逐步算出）。
-- 本引理把两者接起来 ⇒ 侧条件可**直接消费** ✓
--------------------------------------------------------------------------------

interpC-end : ∀ {n : ℕ} (u : T6Vec n) (w : CWalk n)
            → proj₁ (interpC u w) ≡ foldT u w
interpC-end u []       = refl
interpC-end u (s ∷ ws) = interpC-end (ctarget u s) ws

-- ★ 侧条件的 `foldT` 形态（由 `interpC-end` 直接改写）
StepSide-fold : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → Set
StepSide-fold u c = foldT u (srcCode c) ≡ foldT u (tgtCode c)

--------------------------------------------------------------------------------
-- §5. ★★★ 走层拆解（**已证**）：`Σ` 投影 ↔ 可计算端点
--
-- ## 桥一：把 `interpC` 的走沿 `interpC-end` 运到 `foldT` 端点 = `interpAt` 的走
--
-- `proj₁ (interpC u w)` 是 **`Σ` 的投影**（stuck 项），`foldT u w` 会计算 ⇒ 两者只由
-- `interpC-end` 相等 ⇒ 必须沿它运输。
-- **方向**：`interpC-end u w : proj₁ … ≡ foldT …`，而 `interpAt u w` 落在 `foldT` 侧
-- ⇒ 只有把**左端**运到 `foldT` 才类型正确（反向须 `sym`；写反的真报错格式见 §3 的负向对照）。
-- 证明：`T6CayleyInterp.subst-cons` + 归纳。
--------------------------------------------------------------------------------

interpC-walk : ∀ {n : ℕ} (u : T6Vec n) (w : CWalk n)
             → subst (λ v → Walk (T6CayleySym n) u v) (interpC-end u w)
                     (proj₂ (interpC u w))
               ≡ interpAt u w
interpC-walk u []       = refl
interpC-walk u (s ∷ ws) =
  trans (subst-cons (cEdge u s) (proj₂ (interpC (ctarget u s) ws))
                    (interpC-end (ctarget u s) ws))
        (cong (cons (cEdge u s)) (interpC-walk (ctarget u s) ws))

--------------------------------------------------------------------------------
-- ## 桥二：走层的 `++` 分配律（本模块原 §5 想要的陈述，**已证**）
--
-- 对 `a` 归纳：`[]` 情形 `interpC-++ u [] b = refl` **定义性** ⇒ `subst P refl X = X`；
-- `s ∷ a` 情形 `interpC-++ u (s ∷ a) b` 归约到 `interpC-++ (ctarget u s) a b`（定义性）
-- ⇒ 归纳假设直接 `cong` 到 `cons` 下（与 `T6CayleyInterp.interpAt-++` 同形）。
--------------------------------------------------------------------------------

interpC-++-walk : ∀ {n : ℕ} (u : T6Vec n) (a b : CWalk n)
                → proj₂ (interpC u (a ++ b))
                  ≡ proj₂ (interpC u a) ++w
                    subst (λ v → Walk (T6CayleySym n) (proj₁ (interpC u a)) v)
                          (sym (interpC-++ u a b))
                          (proj₂ (interpC (proj₁ (interpC u a)) b))
interpC-++-walk u []      b = refl
interpC-++-walk u (s ∷ a) b = cong (cons (cEdge u s)) (interpC-++-walk (ctarget u s) a b)

--------------------------------------------------------------------------------
-- §6. ⬜ 下一个节点：`StepCode → AStep`（判据明确，前置已齐）
--
-- 目标形状（`h` 把靶走的端点搬到源走端点，`ASTep` 才允许居留）：
-- ```
--   toStepCode : (u : T6Vec n) (c : StepCode n) (h : StepSide u c)
--              → AStep (T6CayleySym n) (proj₂ (interpC u (srcCode c)))
--                                      (subst (λ v → Walk (T6CayleySym n) _ v) h
--                                             (proj₂ (interpC u (tgtCode c))))
-- ```
-- **已有前置**：`interpC-walk`（把两条走搬到 `interpAt` 形态）、
-- `T6CayleyInterp.toStep`（`interpAt` 形态的 `ASTep` 构造，参数为 `pref`/`s1`/`s2`/`s3`/`suff` + 侧条件）、
-- `subst-cons` / `subst-++w`（端点运输）。
-- **剩余技术点（`[未验证·路线推测]`）**：把 `StepSide`（`proj₁` 形态）改写为
-- `T6CayleyInterp.toStep` 需要的 `ctarget` 形态 —— 需先用 `foldT-++` /
-- `interpC-end` 把 `foldT u (pref ++ (s1 ∷ s2 ∷ suff))` 归约成
-- `foldT (ctarget (ctarget (foldT u pref) s1) s2) suff`，再与 `toStep` 的侧条件对齐。
-- 本批**未做**（本批只交 §5 的两条桥，均已编译通过）。
--------------------------------------------------------------------------------
