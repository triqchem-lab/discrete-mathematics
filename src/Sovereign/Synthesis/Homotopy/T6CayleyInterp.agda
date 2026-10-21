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
open import Data.Fin using (zero)
open import Data.Vec.Base using () renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (DiGraph; Walk; nil; cons; _++w_; AStep; slide)
open DiGraph using (V; edge)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk
  using (ctarget; foldT; cEdge; foldT-++)

--------------------------------------------------------------------------------
-- §0. ★★ 前置：`foldT` 的拼接律 —— **复用**（不自证）
--
-- ```
--   foldT u (a ++ b) ≡ foldT (foldT u a) b        （= T6CayleyCodeWalk.foldT-++）
-- ```
-- 这是 `interpAt-++` 的根因等式：两边 `Walk` 的**终点**差它
-- ⇒ 必须显式 `subst`（经验库 `projection-stuck-let` 的误判防护：「需要 `subst`」）。
--
-- ⚠ 本模块**不重证**它 —— 由 §import 的 `using (… foldT-++)` 引入。
--   历史：初版曾在此重复证一遍，经并行协作者指出后删除（见其后的说明段）。
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
-- §3b. 派生的**消费形态**：把内层 `subst` 提到整式外（下游拼两步时更好用）
--
-- 拼接律原始形态把 `subst` 留在**第二个走**里；对消费者而言通常是
-- 「先各自解释、再 `++w`，最后整体搬端点」。两者等价，见 `interpAt-++-glue`。
--------------------------------------------------------------------------------

-- `subst` 沿终点与 `++w` 交换（对左 `p` 归纳；`cons` 情形用 §1b 的 `subst-cons`）
subst-++w : ∀ {n : ℕ} {u m : T6Vec n} (p : Walk (T6CayleySym n) u m)
            {a b : T6Vec n} (eq : a ≡ b) (q : Walk (T6CayleySym n) m a)
          → subst (λ v → Walk (T6CayleySym n) u v) eq (p ++w q)
            ≡ p ++w subst (λ v → Walk (T6CayleySym n) m v) eq q
subst-++w (nil m) eq q = refl
subst-++w (cons c p) eq q =
  trans (subst-cons c (p ++w q) eq) (cong (cons c) (subst-++w p eq q))

interpAt-++-glue : ∀ {n : ℕ} (u : T6Vec n) (a b : CWalk n)
                 → interpAt u (a ++ b)
                   ≡ subst (λ v → Walk (T6CayleySym n) u v) (sym (foldT-++ u a b))
                           (interpAt u a ++w interpAt (foldT u a) b)
interpAt-++-glue u a b =
  trans (interpAt-++ u a b)
        (sym (subst-++w (interpAt u a) (sym (foldT-++ u a b))
                        (interpAt (foldT u a) b)))

--------------------------------------------------------------------------------
-- §4. 〔历史·已被 §6 取代〕初版对「步 7 忠实性」的分析框架
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
-- §5. 〔历史·见 §6〕`toStep` 与 `h` 无关的初版两段式
--------------------------------------------------------------------------------

stepE3-irrel : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s3 : CStep n) {z : T6Vec n}
               (h h' : ctarget (foldT u pref) s3 ≡ z)
             → stepE3 u pref s3 {z = z} h ≡ stepE3 u pref s3 {z = z} h'
stepE3-irrel {n} u pref s3 h h' =
  subst-irrel {n} (λ w → T6SymEdge (foldT u pref) w) h h' (cEdge (foldT u pref) s3)

--------------------------------------------------------------------------------
-- §6. ★★★ 步 7：`toStep` 与侧条件证明 `h` **无关**（忠实性 —— 已证）
--
-- ## 陈述本身就是异质相等（必须用 `subst` 表述）
--
-- `toStep … h` 的**返回类型依赖 `h`**（第二个走里含 `stepE3 … h`）⇒
-- `cong` 不适用（它要求余定义域与参数无关，已实测 2 次）✓ 这一步的判读是对的。
-- 正确写法是先搬类型：
-- ```
--   subst (λ e → AStep G src (tgt e)) (stepE3-irrel … h h') (toStep … h) ≡ toStep … h'
-- ```
--
-- ## ★ 更正（`[定理]`：`slide-subst`）：这**不是**「异质相等的标准困难」
--
-- 先前的判定「`subst` 沿 `e` 作用在 `slide … e` 上**不归约** ⇒ 需 `HEq` / `J`」**不成立**：
-- 一般 `q` 下确实不归约，但**证明时对 `q` 模式匹配到 `refl`** —— 此时 `e3' := e3` 被强制，
-- 而 `subst P refl x = x` **定义性**成立 ⇒ 两边一起归约到同一个 `slide` 项 ✓
-- ⇒ 无需 `HEq`、无需 `J`、也无需额外 UIP（`UIP` 只在 `stepE3-irrel` 那层用到了）。
--
-- 一般引理（与具体图形无关；若其他模块也要用，可上提到 `BarceloAHomotopy`）：
--------------------------------------------------------------------------------

slide-subst : ∀ {G : DiGraph} {u x z v y : V G}
              (p : Walk G u x) (b : Walk G z v)
              (e1 : edge G x y) (e2 : edge G y z) {e3 e3' : edge G x z}
              (q : e3 ≡ e3')
            → subst (λ e → AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e b)))
                    q (slide p b e1 e2 e3)
              ≡ slide p b e1 e2 e3'
slide-subst p b e1 e2 refl = refl

toStep-irrel : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 s3 : CStep n)
               (suff : CWalk n)
               (h h' : ctarget (foldT u pref) s3
                       ≡ ctarget (ctarget (foldT u pref) s1) s2)
             → subst (λ e → AStep (T6CayleySym n)
                                 (interpAt u pref ++w
                                   (cons (stepE1 u pref s1)
                                         (cons (stepE2 u pref s1 s2)
                                               (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff))))
                                 (interpAt u pref ++w
                                   (cons e (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff))))
                     (stepE3-irrel u pref s3 {z = ctarget (ctarget (foldT u pref) s1) s2} h h')
                     (toStep u pref s1 s2 s3 suff h)
               ≡ toStep u pref s1 s2 s3 suff h'
toStep-irrel u pref s1 s2 s3 suff h h' =
  slide-subst (interpAt u pref)
              (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff)
              (stepE1 u pref s1) (stepE2 u pref s1 s2)
              (stepE3-irrel u pref s3 h h')

--------------------------------------------------------------------------------
-- §6b. 〔修订后的判定〕归约**不需要** §6 的等式（`[判断·非定理]`；§6 已由 `slide-subst` 证成）
--
-- `reduce` 只需要 **可靠性**：同一个码 ⇒ 同一步。`toStep` 本来就是
-- `(u, pref, s1, s2, s3, suff, h)` 的**函数** ⇒ 同码（含同一个 `h`）给出同一个项，
-- 可靠性**定义性成立** ✓。**忠实性**（不同码 ⇒ 不同步）才用到 §6 的等式，
-- 而它现在也有了（`toStep-irrel`）✓。
--
-- ⇒ 步 1–7 全部有内核回执；`toStep-irrel` 由「未实施」改为**已证**。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §7. ★★★ 对抗验证（纪律 §6）：在**具体点**上实例化整条链
--
-- 取 `n = 1`、起点 = 全零向量、前缀/后缀都空，
-- 三步取 **三角形**：`+e₀`、`+e₀`、`−e₀`（`−e₀` 从 `x` 到 `x+2e₀`）
-- ⇒ 侧条件**两边算到同一个顶点** ✓
--
-- 三样都必须是 `refl`（不是「论证」，是**计算**）：
--   ① 侧条件在具体点成立；② `foldT` 的具体值；③ 整条 `toStep` **有类型**。
--------------------------------------------------------------------------------

x1 : T6Vec 1
x1 = zero ∷ᵥ []ᵥ

-- ① 侧条件（三角形闭合）—— `refl`
side-ok : ctarget (ctarget x1 (cplus zero)) (cplus zero)
        ≡ ctarget x1 (cminus zero)
side-ok = refl

-- ② 走一步的终点—— `refl`
endpoint-1 : foldT x1 (cplus zero ∷ []) ≡ updAt zero x1
endpoint-1 = refl

-- ③ ★ 整条 `toStep` 在具体点**有类型**（并因此产出真实的 `ASTep` 值）
step-1 : AStep (T6CayleySym 1)
           (interpAt x1 [] ++w
             (cons (stepE1 x1 [] (cplus zero))
                   (cons (stepE2 x1 [] (cplus zero) (cplus zero))
                         (interpAt (ctarget (ctarget x1 (cplus zero)) (cplus zero)) []))))
           (interpAt x1 [] ++w
             (cons (stepE3 x1 [] (cminus zero) side-ok)
                   (interpAt (ctarget (ctarget x1 (cplus zero)) (cplus zero)) [])))
step-1 = toStep x1 [] (cplus zero) (cplus zero) (cminus zero) [] side-ok
