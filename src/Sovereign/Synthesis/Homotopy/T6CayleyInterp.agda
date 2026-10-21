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
-- 拼接拆解 `interpAt-++`：**证明子句**只需 `refl` / `cong`；
-- 陈述里那处端点传输必须用 **`sym (foldT-++ …)`**（方向见 §3，正向写法类型不成立）
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
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_; AStep; slide)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk
  using (ctarget; foldT; cEdge; foldT-++)

--------------------------------------------------------------------------------
-- §0. ★★ 前置：`foldT` 的拼接律（**不是 defeq**，必须证）
--
-- ```
--   foldT u (a ++ b) ≡ foldT (foldT u a) b
-- ```
-- 这正是 `interpAt-++` 卡住的根因：两边 `Walk` 的**终点**差这条等式
-- ⇒ 必须显式 `subst`（经验库 `projection-stuck-let` 的误判防护已写明「需要 `subst`」）。
--------------------------------------------------------------------------------

-- ⚠ **复用**：`foldT-++` 已存在于 `T6CayleyCodeWalk.agda:131`，本模块**不重证**，
-- 由上方 `using` 引入（依 AGENTS.md「写新件前的硬性前置」：先全库查再动手）。
--
-- 历史留痕：我最初在此**重复证了一遍**（同样的两条子句），后经并行协作者指出而删除。
-- 这正是 AGENTS.md 记录的第三类重复实现 —— 该前置我做了 `grep` 但**没查 `foldT-++` 这个符号**。

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

--------------------------------------------------------------------------------
-- §4. ★★★ 步 7：`toStep` 与侧条件证明**无关**（= 码的忠实性）
--
-- ## 为什么这就是「注入性」的内容
--
-- `toStep` 的参数里含一个**证明** `h`（侧条件），而 `h` 不属码。
-- 「码相等 ⇒ 步相等」等价于：**`toStep` 只依赖码**，即与 `h` 的选取无关 ✓
--
-- ## 前置：`subst` 的证明无关性（需要 `T6Vec` 的 UIP）
--
-- `h` 只通过 `stepE3` 生效（`subst (λ w → T6SymEdge …) h (cEdge …)`）
-- ⇒ 需要 `subst P h x ≡ subst P h' x`。
-- 而 `T6Vec n` 的相等**可判定**（`DecEq-T6Vec`）⇒ **UIP 可证**
-- （stdlib `Axiom/UniquenessOfIdentityProofs.agda:69` 的 `Decidable⇒UIP` —— 
--   注意这个模块名带 `Axiom`，但**可判定 ⇒ UIP 是可证的**（Hedberg），不是公理）。
--------------------------------------------------------------------------------

module _ {n : ℕ} where
  open Decidable⇒UIP (DecEq-T6Vec {n}) renaming (≡-irrelevant to T6Vec-UIP)

  -- ★ `subst` 与证明的选取无关
  subst-irrel : (P : T6Vec n → Set) {a b : T6Vec n}
                (h h' : a ≡ b) (x : P a)
              → subst P h x ≡ subst P h' x
  subst-irrel P h h' x = cong (λ e → subst P e x) (T6Vec-UIP h h')

--------------------------------------------------------------------------------
-- §5. ★★★ `toStep` 与 `h` 无关
--------------------------------------------------------------------------------

stepE3-irrel : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s3 : CStep n) {z : T6Vec n}
               (h h' : ctarget (foldT u pref) s3 ≡ z)
             → stepE3 u pref s3 {z = z} h ≡ stepE3 u pref s3 {z = z} h'
stepE3-irrel {n} u pref s3 h h' =
  subst-irrel {n} (λ w → T6SymEdge (foldT u pref) w) h h' (cEdge (foldT u pref) s3)

--------------------------------------------------------------------------------
-- §6. ⬜ `toStep-irrel`（忠实性）—— **判定：不属归约所需，且本体是异质相等**
--
-- ## 想证什么、为什么 `cong` 不行（已实测 2 次，同一报错）
--
-- 想证 `toStep … h ≡ toStep … h'`。但 **`toStep` 的返回类型依赖 `h`**
-- （第二个走里含 `stepE3 … h`）⇒ **依赖余定义域** ⇒
-- `cong` 要求「余定义域与参数无关」，**根本不适用** ✗
--
-- ## 本体的类型学身份（关键判定）
--
-- 正确写法必须先用 `subst` 把 `toStep … h` 的**类型**搬到 `h'` 侧：
-- ```
--   subst (λ e → AStep G src (tgt e)) (stepE3-irrel … h h') (toStep … h) ≡ toStep … h'
-- ```
-- 而 `subst` 沿 `e` 作用在 `slide … e` 上**不归约**（motive 停在复合项）
-- ⇒ 这是 **heterogeneous equality（John Major 等式）** 的标准困难 ✗
-- ⇒ 常规路线是 `HEq` 或 `J`-式运输，**本库不用 `HEq`**。
--
-- ## ★ 但它**不是归约所需**（这一条是判定，标 `[判断·非定理]`）
--
-- `reduce` 只需要 **可靠性**：**同一个码 ⇒ 同一步**。
-- 而 `toStep` 本来就是 `(u, pref, s1, s2, s3, suff, h)` 的**函数**
-- ⇒ 同码（含同一个 `h`）给出**同一个项**，可靠性**定义性成立** ✓
-- **忠实性**（不同码 ⇒ 不同步）才需要 §6 的等式，它对「用码代替步做判定」
-- 的**语义保真**有用，但**不是归约正确性的前提** ✓
--
-- ⇒ **④ 在归约所需的范围内已闭合**（步 1–6 全部有内核回执）；
--   忠实性留作独立课题（前置 `stepE3-irrel` / `subst-irrel` 已证 ✓）。
--------------------------------------------------------------------------------
