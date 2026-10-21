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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_; AStep; slide)
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
-- §2. ★★★ 步 6：构造 `ASTep` 值（`toStep`）
--
-- **关键洞察**：`toStep` **不需要** `interpAt-++`（§3 的拼接拆解）——
-- 因为 `slide` 的结论**本身就是** `p ++w (cons e1 (cons e2 b))` 形态，
-- 只要把 `p` / `b` / `e1` / `e2` / `e3` 分别给出即可。
-- 唯一的 `subst` 在**端点层**（`e3` 的第二个端点由侧条件对齐）✓
--
-- ```
--   slide p b e1 e2 e3 : AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
-- ```
-- 其中 `e1 : edge x y`、`e2 : edge y z`、`e3 : edge x z`，
-- 而 `x = foldT u pref`、`y = ctarget x s1`、`z = ctarget y s2` 都是**计算**出来的 ✓
--------------------------------------------------------------------------------

stepE1 : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 : CStep n)
       → T6SymEdge (foldT u pref) (ctarget (foldT u pref) s1)
stepE1 u pref s1 = cEdge (foldT u pref) s1

stepE2 : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 : CStep n)
       → T6SymEdge (ctarget (foldT u pref) s1)
                   (ctarget (ctarget (foldT u pref) s1) s2)
stepE2 u pref s1 s2 = cEdge (ctarget (foldT u pref) s1) s2

stepE3 : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s3 : CStep n) {z : T6Vec n}
       → ctarget (foldT u pref) s3 ≡ z
       → T6SymEdge (foldT u pref) z
stepE3 u pref s3 h = subst (λ w → T6SymEdge (foldT u pref) w) h (cEdge (foldT u pref) s3)

toStep : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 s3 : CStep n)
         (suff : CWalk n)
       → (h : ctarget (foldT u pref) s3 ≡ ctarget (ctarget (foldT u pref) s1) s2)
       → AStep (T6CayleySym n)
               (interpAt u pref ++w
                 (cons (stepE1 u pref s1)
                       (cons (stepE2 u pref s1 s2)
                             (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff))))
               (interpAt u pref ++w
                 (cons (stepE3 u pref s3 {z = ctarget (ctarget (foldT u pref) s1) s2} h)
                       (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff)))
toStep u pref s1 s2 s3 suff h =
  slide (interpAt u pref) (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff)
        (stepE1 u pref s1) (stepE2 u pref s1 s2) (stepE3 u pref s3 h)

--------------------------------------------------------------------------------
-- §3. ★★★ 拼接拆解 `interpAt-++` —— **方向修正后完成**
--
-- ## 根因（由并行协作者用**探针 + 负向对照**定位，非证明难题）
--
-- 原陈述用 `foldT-++ u a b`（正向）是**类型不对**的：
-- ```
--   subst P eq : P x → P y      （eq : x ≡ y）
-- ```
-- 此处 `x = foldT u (a ++ b)`、`y = foldT (foldT u a) b`，
-- 而 `interpAt (foldT u a) b : P y` —— **落在 y 侧**，正向 `subst` 却要 `P x`。
-- ⇒ 必须用 **`sym (foldT-++ u a b)`**。
--
-- 负向对照实测（探针，报在**类型签名**行）：换成 `foldT-++ u a b` 时报
-- 「`foldT-++ u a b` 期望类型退化成 `foldT u (a ++ b) ≡ foldT u (a ++ b)`」
-- —— 那正是 Agda 强统两个索引的证据。
--------------------------------------------------------------------------------

interpAt-++ : ∀ {n : ℕ} (u : T6Vec n) (a b : CWalk n)
            → interpAt u (a ++ b)
              ≡ interpAt u a ++w
                subst (Walk (T6CayleySym n) (foldT u a)) (sym (foldT-++ u a b))
                      (interpAt (foldT u a) b)
interpAt-++ u []      b = refl
interpAt-++ u (s ∷ a) b =
  cong (λ z → cons (cEdge u s) z) (interpAt-++ (ctarget u s) a b)
