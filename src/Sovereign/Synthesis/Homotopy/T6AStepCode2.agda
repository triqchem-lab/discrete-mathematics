{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepCode2
--
-- **④ 探针的修正**：`AStepCode` 需要**六**组件，不是三组件
--
-- ## 我上批漏了什么（已查 `BarceloAHomotopy.agda:50-56` 的真实定义）
--
-- ```
--   slide  : ∀ {u x y z v} (p : Walk G u x) (b : Walk G z v)
--          → (e1 : edge G x y) (e2 : edge G y z) (e3 : edge G x z)
--          → AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
-- ```
-- ⇒ 一步的**显式参数**是 `p`、`b`、**`e1`、`e2`、`e3`** 共 5 个。
--   我上批的码 `ADir × CWalk × CWalk` **只码了 `p` 和 `b`**，**漏了中间三条边** ✗
--
-- ## 修正后的码
--
-- ```
--   StepCode n = ADir × CWalk n × CStep n × CStep n × CStep n × CWalk n
--                （方向，前缀，e1，e2，e3，后缀）
-- ```
-- 其中每条边用 **`CStep`**（方向 + 坐标）码 —— 因为**给定起点顶点，
-- 一条边由「方向 + 坐标」唯一确定，且见证是 `refl`**
-- （与 `T6CayleyCodeWalk.cEdge` 同一手法）✓
--
-- ## ★ 一个好消息（比上批更乐观的部分）
--
-- 中间三条边既然是**显式参数**，就不需要「在图中搜索三角形」
-- ⇒ 码 → 步的映射**不需要 `Maybe`**（前提是码里带足分量 + 起点）✓
-- 这比上批记的「需搜索、需 `Maybe`」要好。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 复用 `T6CayleyCode` 的 `CStep`/`CWalk`/`DecEq-CStep`/`DecEq-CWalk` 与 `T6AStepCode.ADir`

module Sovereign.Synthesis.Homotopy.T6AStepCode2 where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
import Data.Fin as DF
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cplus; cminus; DecEq-CStep; DecEq-CWalk)
open import Sovereign.Synthesis.Homotopy.T6AStepCode using (ADir; dslide; dexpand; DecEq-ADir)

--------------------------------------------------------------------------------
-- §1. 六组件码（构造子形式，方便 `cong` 链）
--------------------------------------------------------------------------------

data StepCode (n : ℕ) : Set where
  mkStep : (dir : ADir) (pref : CWalk n)
           (e1 e2 e3 : CStep n) (suff : CWalk n)
         → StepCode n

--------------------------------------------------------------------------------
-- §2. ★★ 可判定相等（6 层 `with` + 6 个 `cong` 的一条 `trans` 链）
--------------------------------------------------------------------------------

DecEq-StepCode : ∀ {n : ℕ} (s s' : StepCode n) → Dec (s ≡ s')
DecEq-StepCode (mkStep d w a b c f) (mkStep d' w' a' b' c' f')
  with DecEq-ADir d d'
... | no  ¬p = no λ { refl → ¬p refl }
... | yes p1 with DecEq-CWalk w w'
...   | no  ¬p = no λ { refl → ¬p refl }
...   | yes p2 with DecEq-CStep a a'
...     | no  ¬p = no λ { refl → ¬p refl }
...     | yes p3 with DecEq-CStep b b'
...       | no  ¬p = no λ { refl → ¬p refl }
...       | yes p4 with DecEq-CStep c c'
...         | no  ¬p = no λ { refl → ¬p refl }
...         | yes p5 with DecEq-CWalk f f'
...           | no  ¬p = no λ { refl → ¬p refl }
...           | yes p6 =
  yes (trans (cong (λ z → mkStep z w a b c f) p1)
       (trans (cong (λ z → mkStep d' z a b c f) p2)
       (trans (cong (λ z → mkStep d' w' z b c f) p3)
       (trans (cong (λ z → mkStep d' w' a' z c f) p4)
       (trans (cong (λ z → mkStep d' w' a' b' z f) p5)
              (cong (λ z → mkStep d' w' a' b' c' z) p6))))))

--------------------------------------------------------------------------------
-- §3. ⬜ 下一步（判据明确）
--
-- ① **码 → 步的映射**（**不需要 `Maybe`**，见上）：
--    `toStep : (x : T6Vec n) (c : StepCode n)
--            → Maybe (Σ (λ (p q : Walk (T6CayleySym n) ? ?) → AStep (T6CayleySym n) p q))`
--    用 `T6CayleyCodeWalk.cEdge`（见证 = `refl`）把三个 `CStep` 变成三条边；
--    ⚠ 仍需起点顶点推出 `x, y, z` 的坐标 —— 但那是**计算**（`ctarget`），不是搜索 ✓
-- ② **单射性**：码相等 ⇒ 步相等（需证明 `toStep` 在有效码上单射）。
--
-- 本模块只交码与可判定相等。
--
-- ## 更新（2026-10-21，跨模块核对后的真实状态）
--
-- ① **码 → 步的映射已经存在**：不在本模块，而在
--    `Sovereign.Synthesis.Homotopy.T6CayleyInterp.toStep`
--    （`(u) (pref) (s1 s2 s3) (suff) (h : ctarget (foldT u pref) s3 ≡ ctarget (ctarget (foldT u pref) s1) s2)
--      → AStep (T6CayleySym n) (interpAt u pref ++w cons e1 (cons e2 b)) (interpAt u pref ++w cons e3 b)`），
--    并已由 `toStep-irrel` 证「与侧条件证明的选取无关」。
-- ② **若想把映射直接陈述在 `StepCode` 上**：`stepE1/E2/E3` + `StepVertex` 在
--    `Sovereign.Synthesis.Homotopy.T6AStepMap`（那里也证明了 `StepSide ⇔ StepVertex` 与可判定性）。
-- ③ ✅ **「先造 `interpC` 再搬运」这条路线已经走通**（原注在此写「ill-posed 别再试」，**已作废**）：
--      `T6AStepCodeMap.toStepCode` 证成了它，关键是 `cons-dtrans` —— 沿**中间顶点**的依赖运输，
--      而 `subst-cons` 只覆盖端点运输（后者曾被误当成唯一分解）。
--    （`subst-cons` 只搬走层端点、不动头边索引 ⇒ 自然走头边 `cEdge x s3` 与 `slide` 需要的
--    顶点铸造边 `e3` **类型就不同**，不存在把它们等同的等式）。要做码→A-同伦请**以 `interpAt` 为载体**。
-- ④ 单射性（不同码 ⇒ 不同步）仍需 `StepCode` 的可判定相等**可靠性**支撑 —— 见下条待办。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4. ★★★ 判定器的**可靠性**：`yes` ⇒ 真的相等（TSet-反射，非 64 案穷举）
--
-- `DecEq-StepCode` 是六层 `with` 串联的判定器，此前**没有任何正确性证明** ——
-- 一个没被验证过的判定器，下游用它的 `yes` 就等于用公理。
--
-- 证法：引入反射型 `TSet`（`yes` 时断言命题、`no` 时断言空），
-- 再让证明的 `with` 结构与定义**逐层对齐** ⇒ 每个 `no` 分支假设为 `⊥`（`λ ()` 消去），
-- 唯一的 `yes` 分支用与定义同形的 6 条 `cong` 链复原等式 ✓
-- （**12 个子句**，不是 2⁶=64 案枚举；且避开了 `DecEq-CStep` 的 UIP/funext 墙 ——
--   见台账 `PN.B4.deceq-reflection-wall`，那是**另一条**性质，本条不需要它。）
--
-- ✅ 反方向（相等 ⇒ `yes`，即**完备性**）**已证**：`DecEq-StepCode-complete`（同模块 §5：
--    先 J 到自反参数，再 `StepCode-refl`；各分量判定器的自反性已逐个给出）
-- （`DecEq-ADir`/`DecEq-CStep`/`DecEq-CWalk` 的完备性），本模块未提供。
--------------------------------------------------------------------------------
-- §3b. `Dec` 的反射型（`yes` 时断言命题、`no` 时断言空）—— 两个方向都要用它
--------------------------------------------------------------------------------

TSet : ∀ {A : Set} → Dec A → Set
TSet {A = A} (yes _) = A
TSet (no _)  = ⊥

--------------------------------------------------------------------------------
-- §4. ★★★ 判定器的**可靠性 + 完备性**（各一行：`with` 判定器本身）
--
-- 关键洞察（本会话两次踩过才想明白）：**直接 `with` 判定器的返回值**，
--   · `yes p` 支：`TSet (yes p)` 归约为命题本身 ⇒ `p` 就是证据；
--   · `no ¬p` 支：`TSet (no ¬p)` 归约为 `⊥`，而 `¬p` 本身就是「命题不成立」的证明
--     ⇒ 两个方向都**不需要**任何结构归纳、不需要分量判定器的自反性引理。
--
-- 早期版本为此写了 6 层 `with` + `ADir-refl`/`Fin-refl`/`CStep-refl`/`CWalk-refl`/
-- `StepCode-refl` 共 ~85 行——**全部不必要**，已删除。
--------------------------------------------------------------------------------

DecEq-StepCode-sound : ∀ {n : ℕ} (s s' : StepCode n) → TSet (DecEq-StepCode s s') → s ≡ s'
DecEq-StepCode-sound s s' h with DecEq-StepCode s s'
... | yes p  = p
... | no  ¬p = ⊥-elim h

DecEq-StepCode-complete : ∀ {n : ℕ} (s s' : StepCode n) → s ≡ s' → TSet (DecEq-StepCode s s')
DecEq-StepCode-complete s s' h with DecEq-StepCode s s'
... | yes p  = p
... | no  ¬p = ⊥-elim (¬p h)
