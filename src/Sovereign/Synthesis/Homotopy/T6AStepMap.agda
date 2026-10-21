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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (interpC; ctarget; foldT; cEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_)
open import Sovereign.Synthesis.Homotopy.T6AStepCode2 using (StepCode; mkStep)

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
-- §5. ⬜ 第 5 步（走层拆解）—— **未完成，本批尝试已撤回（如实记录）**
--
-- 想要的陈述（对 `a` 归纳）：
-- ```
--   proj₂ (interpC u (a ++ b))
--     ≡ proj₂ (interpC u a) ++w proj₂ (interpC (proj₁ (interpC u a)) b)
-- ```
--
-- ## ⚠ 我判断错了（自纪）：一度以为「不需要 `subst`」
--
-- 理由曾是「`interpC` 与 `foldT` 都按 `ctarget` 递归 ⇒ 端点定义性相同」。
-- **错**：`proj₁ (interpC u a)` 是 **`Σ` 的投影**（stuck 项），
-- 而 `foldT u a` 会计算 ⇒ 两者**不是定义性相等**
-- （`interpC-end` 是 `refl` 级只说明「逐点相等」，不说明投影项可归约）。
--
-- ⇒ 正确的陈述必须显式携带 `subst`：
-- ```
--   Σ (λ (h : proj₁ (interpC u (a ++ b)) ≡ proj₁ (interpC (proj₁ (interpC u a)) b))
--       → subst (Walk G u) h (proj₂ (interpC u (a ++ b)))
--         ≡ proj₂ (interpC u a) ++w proj₂ (interpC (proj₁ (interpC u a)) b))
-- ```
-- 而 `cons` 情形的归纳要在 `cong` 之外再穿一次 `subst` —— 本批**未写成**。
--
-- 已撤回的半成品：不做「编译不绿」的交易；本模块停在上一个绿基线（`a958d82c`）。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §5. ⬜ 下一步（判据明确，**已定位到唯一的技术关**）
--
-- `toStep` 的陈述形状：
-- ```
--   toStep : (u) (c : StepCode n) (h : StepSide u c)
--          → AStep (T6CayleySym n) (proj₂ (interpC u (srcCode c)))
--                                  (proj₂ (interpC u (tgtCode c)))
-- ```
-- **技术关**：`ASTep G p q` 要求 `p q : Walk G U V` **端点相同**；
-- 而两个 `proj₂` 的端点是 `proj₁` 的形式，只由 `h` 相等
-- ⇒ 必须 **`subst` on `Walk`**（把靶走的端点索引沿 `h` 运输）。
--
-- ⇒ 这就是第 5 步：把 `interpC-++`/`interpC-end` 的**端点层**结论升级到
--   **走层**（对 `Walk` 做 `subst`）。本批**未做**，如实保留。
--------------------------------------------------------------------------------
