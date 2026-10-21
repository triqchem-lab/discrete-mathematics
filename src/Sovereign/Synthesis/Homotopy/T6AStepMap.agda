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
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode
  using (CStep; CWalk; cplus; cminus; cstep-inv)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (interpC; ctarget; foldT; cEdge; foldT-++; ctarget-inv)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using (Walk; nil; cons; _++w_; AStep)
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

-- ★ §4 声称「把两者接起来」，但此前只证了 `interpC-end`；这里补上**等价的一侧**
-- （另一侧 `StepSide→fold` 在 §5c）。合起来 `StepSide u c ⇔ StepSide-fold u c`。
StepSide-fold→StepSide : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n)
                       → StepSide-fold u c → StepSide u c
StepSide-fold→StepSide u c h =
  trans (interpC-end u (srcCode c))
        (trans h (sym (interpC-end u (tgtCode c))))

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

-- `subst` 的逆：沿 `sym e` 把沿 `e` 的运输原样剥掉（对 `e` 匹配到 `refl` 即 `refl`）
subst-sym-inv : ∀ {A : Set} (P : A → Set) {x y : A} (e : x ≡ y) (X : P x)
              → subst P (sym e) (subst P e X) ≡ X
subst-sym-inv P refl X = refl

-- `interpC-walk` 的**反向形态**：直接给出 `proj₂ (interpC u w)` 的 `interpAt` 表达式
interpC-walk' : ∀ {n : ℕ} (u : T6Vec n) (w : CWalk n)
              → proj₂ (interpC u w)
                ≡ subst (λ v → Walk (T6CayleySym n) u v) (sym (interpC-end u w))
                        (interpAt u w)
interpC-walk' {n} u w =
  trans (sym (subst-sym-inv (λ v → Walk (T6CayleySym n) u v)
                            (interpC-end u w) (proj₂ (interpC u w))))
        (cong (subst (λ v → Walk (T6CayleySym n) u v) (sym (interpC-end u w)))
              (interpC-walk u w))

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
-- §5b. ★★★ 侧条件的**层级**校正：`slide` 要的是**顶点**条件，不是「走端点」条件
--
-- `slide` 的第三边要求 `e3 : edge G x z`，其中 `z` 是 `b` 的**起点** ——
-- 在本编码里恰是「两步之后那个顶点」`Z = ctarget (ctarget x s1) s2`（**顶点层**）。
-- 而原 `StepSide` 说的是两条**完整走**的末端相等（走层，中间隔着 `suff`）。
--
-- **已证**：顶点条件 ⇒ 端点条件（`StepVertex→StepSide`，下面两条）。
-- **未证**（`[未验证·路线推测]`）：反方向需要「`foldT (·) suff` 单射」——
-- 每步 `ctarget (·) s` 都是双射（`updAt j` 或 `updAt j ∘ updAt j`），故应当成立，
-- 但本模块尚未证，是 `toStepCode` 之外的**独立节点**（不是 `toStepCode` 的前置，
-- 因为 `toStepCode` 直接取顶点条件即可）。
--------------------------------------------------------------------------------

StepVertex : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → Set
StepVertex u (mkStep _ pref s1 s2 s3 suff) =
  ctarget (foldT u pref) s3 ≡ ctarget (ctarget (foldT u pref) s1) s2

-- 源码走的 `foldT` 终点（沿 `foldT-++` 三步归约到 `Z` 之后的 `suff`）
foldT-src : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 : CStep n) (suff : CWalk n)
          → foldT u (pref ++ (s1 ∷ s2 ∷ suff))
            ≡ foldT (ctarget (ctarget (foldT u pref) s1) s2) suff
foldT-src u pref s1 s2 suff =
  trans (foldT-++ u pref (s1 ∷ s2 ∷ suff))
        (trans (foldT-++ (foldT u pref) (s1 ∷ []) (s2 ∷ suff))
               (foldT-++ (ctarget (foldT u pref) s1) (s2 ∷ []) suff))

-- 靶码走的 `foldT` 终点（同理两步）
foldT-tgt : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s3 : CStep n) (suff : CWalk n)
          → foldT u (pref ++ (s3 ∷ suff)) ≡ foldT (ctarget (foldT u pref) s3) suff
foldT-tgt u pref s3 suff =
  trans (foldT-++ u pref (s3 ∷ suff)) (foldT-++ (foldT u pref) (s3 ∷ []) suff)

-- 顶点条件 ⇒ 两条走的 `foldT` 终点相等（复用上面两条：源侧归约、把 `h` 送到 `suff` 之后、靶侧归约）
StepVertex→fold : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → StepVertex u c
                → foldT u (srcCode c) ≡ foldT u (tgtCode c)
StepVertex→fold u (mkStep d pref s1 s2 s3 suff) h =
  trans (foldT-src u pref s1 s2 suff)
        (trans (cong (λ v → foldT v suff) (sym h))
               (sym (foldT-tgt u pref s3 suff)))

-- 从而 ⇒ 原有的走端点侧条件
StepVertex→StepSide : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → StepVertex u c
                    → StepSide u c
StepVertex→StepSide u c h =
  trans (interpC-end u (srcCode c))
        (trans (StepVertex→fold u c h) (sym (interpC-end u (tgtCode c))))

--------------------------------------------------------------------------------
-- §5c. ★★★ 反方向：`StepSide ⇒ StepVertex`（§5b 里标 `[未验证·路线推测]` 的那条，**已证**）
--
-- 关键零件：**每步 `ctarget (·) s` 是双射** —— `T6CayleyCodeWalk.ctarget-inv` 正是它的左逆
-- （`ctarget (ctarget x s) (cstep-inv s) ≡ x`，即 GF(3) 三步归零的直接推论）。
-- ⇒ `foldT (·) w` 单射（沿 `w` 归纳）⇒ **走端点相等 ⇒ 顶点相等**。
--
-- 于是 `StepSide ⇔ StepVertex`：原侧条件**并不弱**，只是绕了 `suff` 一圈表达的。
-- 这两个方向合起来也解释了 §5b 的「层级」现象：在同一套定义下两者等价，
-- 但**能直接喂给 `slide` 的是 `StepVertex`**（顶点层），所以 §6 先用 `StepSide→StepVertex` 换层。
--------------------------------------------------------------------------------

-- 每步 `ctarget (·) s` 单射
ctarget-inj : ∀ {n : ℕ} {v v' : T6Vec n} (s : CStep n)
            → ctarget v s ≡ ctarget v' s → v ≡ v'
ctarget-inj {v = v} {v'} s e =
  trans (sym (ctarget-inv v s))
        (trans (cong (λ w → ctarget w (cstep-inv s)) e) (ctarget-inv v' s))

-- 故 `foldT (·) w` 单射
foldT-inj : ∀ {n : ℕ} (w : CWalk n) {v v' : T6Vec n}
          → foldT v w ≡ foldT v' w → v ≡ v'
foldT-inj []       e = e
foldT-inj (s ∷ ws) e = ctarget-inj s (foldT-inj ws e)

-- `StepSide`（走端点）⇒ `foldT` 终点等式
StepSide→fold : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → StepSide u c
              → foldT u (srcCode c) ≡ foldT u (tgtCode c)
StepSide→fold u c h =
  trans (sym (interpC-end u (srcCode c))) (trans h (interpC-end u (tgtCode c)))

-- ★ 走端点相等 ⇒ 顶点条件（用 `foldT (·) suff` 单射，两侧先化成同一形态）
StepSide→StepVertex : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n)
                    → StepSide u c → StepVertex u c
StepSide→StepVertex u (mkStep d pref s1 s2 s3 suff) h =
  sym (foldT-inj suff
        (trans (sym (foldT-src u pref s1 s2 suff))
               (trans (StepSide→fold u (mkStep d pref s1 s2 s3 suff) h)
                      (foldT-tgt u pref s3 suff))))

--------------------------------------------------------------------------------
-- §5e. ★★ `interpAt` 对**起点顶点**的自然性（§6 点名的最后一块前置，**已证**）
--
-- 换起点 `v → v'` 时，只要把**同一处** `z` 在两个端点上都运一次，`interpAt` 就跟着换：
-- ```
--   subst (λ z → Walk G z (foldT z w)) e (interpAt v w) ≡ interpAt v' w
-- ```
-- 证明只需对 `e` 做 `J`：`e := refl` 时 `subst P refl X = X`，两边同归约到 `interpAt v w` ✓
-- （注意 `e : v ≡ v'` 的两端是**不同变量**，不是自反等式 ⇒ `J` 合法）。
--------------------------------------------------------------------------------

interpAt-natural : ∀ {n : ℕ} {v v' : T6Vec n} (e : v ≡ v') (w : CWalk n)
                 → subst (λ z → Walk (T6CayleySym n) z (foldT z w)) e (interpAt v w)
                   ≡ interpAt v' w
interpAt-natural refl w = refl

--------------------------------------------------------------------------------
-- §6. ✅ `StepCode → AStep`：**已证**（本节曾是「ill-posed 不可证」的错误判断，已更正）
--
-- ## 更正（内核裁决，2026-10-21）
--
-- 本节原写「`toStepCode` 的 `interpC` 两端版**不可证**」，理由是
-- `subst-cons` 说「cast 不动头边」⇒ 两条走的头边**类型不同** ⇒ 不可能相等。
--
-- **该推理无效** ✗ —— `toStepCode` **已由 `T6AStepCodeMap.toStepCode` 证成**
-- （0 postulate / 0 hole，回执 `2166490f38aa0a105a9675c6544212736c4f247936a177a62045584a58262af5`）。
--
-- ## 错在哪（这是本节最该记住的）
--
-- `subst-cons` 只给出「沿端点 cast」的**一种**分解：头边不动。
-- 但**同一个 `subst` 项还有第二种分解** —— 走 `cons` 的尾走**终点也依赖中间顶点**
-- ⇒ `cons` 是**依赖**于中间顶点的运算，故还需一条
-- ```
--   cons-dtrans : subst (Walk G A) (cong (λ v → foldT v suff) k) (cons e t)
--               ≡ cons (subst (T6SymEdge A) k e)
--                      (subst (λ v → Walk G v (foldT v suff)) k t)
-- ```
-- ⇒ 把码层靶树的**中间顶点** `Zc` 搬到 `Z`（与 `toStep` 的靶树对齐）后，
--   两条走**确实**相等 ✓
--
-- **教训**：`subst-cons` 那种「一行引理」描述的是**一条**分解路径；
-- **不能**由「这一条分解下头边不动」推出「所有分解下头边都不动」✗
-- （把**某一条**改写规则当成**唯一**改写规则）。
--
-- ## 落点
--
-- - 主定理：`T6AStepCodeMap.toStepCode`（含具体点验证 `step-1`）
-- - 配套：`cons-dtrans` / `interpAt-subst` / `subst-trans` / `T6Vec-UIP` / `src-eq` / `tgt-eq`
-- - ⚠ `astStep-cast` / `decStepVertex` 曾因上述错误判断被删，现已在 `T6AStepCodeMap` 就地补回。
-- ⇒ 若下游需要「码 ⇒ A-同伦」，应当**直接以 `interpAt` 为载体**（`T6CayleyInterp.interpAt`
-- 已是可计算终点版本），而不是先造 `interpC` 再搬运。
--
-- 已备零件（若要按 `interpAt` 层重做）：`interpAt-++` / `interpAt-++-glue`（拼接与端点）、
-- `interpAt-natural`（§5e，换起点）、`subst-cons` / `subst-++w`（走层运输）、
-- `T6CayleyInterp.toStep`（步的构造）。
--------------------------------------------------------------------------------
