{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6AStepCodeMap
--
-- **④ 接线完成**：`StepCode → AStep`（`toStepCode`）—— 码层的「一步」真正落到 `ASTep`
--
-- ## 交付
--
-- | 件 | 内容 |
-- |---|---|
-- | `toStep-vertex-form` | 把 `toStep` 的三条边**展开**成 `cEdge` 形态 ⇒ 显式暴露「侧条件是顶点层」|
-- | `srcCode-glue` | `interpAt u (srcCode c)` 按 `interpAt-++-glue` 展开（1 行）|
-- | `toStepExpand` | `expand` 方向（`toStep` 只造 `slide`）|
-- | `astStep-src` / `astStep-tgt` | `ASTep` 沿**走等式**铸源侧 / 靶侧（一行）|
-- | `cons-dtrans` / `interpAt-subst` / `subst-trans` / `T6Vec-UIP` | 三条一行铸型工具 + Hedberg UIP |
-- | `src-eq` / `tgt-eq` | 码层两条走 ⇄ `interpAt` 形态（两侧各自的完整链）|
-- | **`toStepCode`** | **主定理**：码 + 顶点侧条件 ⇒ `ASTep`（`slide` 方向）|
-- | **`toStepCodeExpand`** | 镜像方向（`expand`）|
-- | **`toAHomotopy` / `toAHomotopyDir`** | 码 ⇒ `AHomotopy`；按 `ADir` 分派（**只能在对称闭包层**分派）|
-- | **`decStepCode`** | `Dec (StepVertex u c)`：`toStepCode` 的前提**可算** |
-- | **`noStepVertex`** | **负向控制**：同向码的侧条件**假** ⇒ `decStepCode` 的 `no` 分支可达 |
--
-- ## ★ 两条经实测的修正（先前判断都不成立）
--
-- ### ① 简报给的签名**类型不成立**：缺 `sym`（负向对照见 §7）
--
-- `StepSide u c : proj₁ (interpC u (srcCode c)) ≡ proj₁ (interpC u (tgtCode c))`，
-- 而 `subst P e : P x → P y`（`e : x ≡ y`）；被运输的 `proj₂ (interpC u (tgtCode c))`
-- 落在 `P y` 侧 ⇒ 正向 `subst` 要 `P x` ⇒ **类型错误**。
-- 唯一良型写法是 `sym (StepVertex→StepSide u c h)`（与 `T6AStepMap` §6 旧注释同方向）。
-- **这不是改弱陈述** —— `sym` 只把等式反向，命题强度不变。
--
-- ### ② 简报的「联合铸型 `astStep-cast₂`」：不需要，且解决不了问题
--
-- 真卡点更下一层：`s2` 的边是 `cEdge Y s2 : T6SymEdge Y Z`（`Z = ctarget (ctarget X s1) s2`），
-- `s3` 的边是 `cEdge X s3 : T6SymEdge X Zc`（`Zc = ctarget X s3`）。
-- 侧条件 `h : Zc ≡ Z` 只是**命题**相等 ⇒ 两条边**不同型** ⇒
-- 「`e3' = subst … h (cEdge X s3)` 等于 `cEdge X s3`」**不成立**（`cons` 的中间索引不同）。
-- 所以不是「铸型方式」问题：**两侧必须归约到同一个中间顶点**。
--
-- ## 解法（§5）：运输**中间顶点**，不是运输走
--
-- `cons e t` 的第二项 `t : Walk G z (foldT z suff)` 的**终点也依赖 z**
-- ⇒ `cons` 是**依赖**于中间顶点 `z` 的运算 ⇒ 一行引理 `cons-dtrans` 同时运输「边」与「尾走」。
-- 于是码层靶走的 `(cEdge X s3, q0)` 沿 `h` 运输后**恰好**是 `toStep` 的 `(e3', b)`
-- （尾走那半由 `interpAt-subst` 一行闭合）⇒ 目标两侧都归约到中间顶点 `Z` 的形态，
-- **一次** `astStep-cast`（同一条端点等式铸两侧）即可 —— 简报的 `astStep-cast₂` 用不上。
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical；不用 `HEq`
--   · 复用 `T6CayleyInterp.toStep` / `T6AStepMap` 的既有件（不重写）

module Sovereign.Synthesis.Homotopy.T6AStepCodeMap where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; _++_)
open import Data.Fin using (zero)
open import Data.Vec.Base using (head) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥)
import Data.Fin as Fin
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)
open import Sovereign.Synthesis.Homotopy.T6CayleyGraph using (succF3)
open import Sovereign.Synthesis.Homotopy.T6CayleyDec using (DecEq-T6Vec)
open import Sovereign.Synthesis.Homotopy.T6CayleyCode using (CStep; CWalk; cplus; cminus)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6CayleySym; T6SymEdge)
open import Sovereign.Synthesis.Homotopy.BarceloAHomotopy using
  (Walk; cons; _++w_; AStep; slide; expand; AHomotopy; AStep⊆AH; AH-symm)
open import Sovereign.Synthesis.Homotopy.T6CayleyCodeWalk using (ctarget; foldT; cEdge; foldT-++; interpC)
open import Sovereign.Synthesis.Homotopy.T6CayleyInterp using (interpAt; x1; toStep; interpAt-++-glue; subst-++w)
open import Sovereign.Synthesis.Homotopy.T6AStepCode using (ADir; dslide; dexpand)
open import Sovereign.Synthesis.Homotopy.T6AStepMap using
  (srcCode; tgtCode; StepVertex; StepSide; StepVertex→StepSide; interpC-walk'; interpC-end)
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
-- **真实缺口**：`T6CayleyInterp.toStep` 的签名**不接收 `ADir`**
-- ⇒ 它只构造 `slide`，**从不构造 `expand`** ✗ —— 于是「码 → 步」只覆盖了 `ASTep` 的一半。
--
-- ⚠ 一个**不可行**的设计（实测否决）：想用 `d : ADir` 分派到**一个**函数。
-- 两个构造子的结论方向**相反**：
-- ```
--   slide  … : AStep G (p ++w (cons e1 (cons e2 b))) (p ++w (cons e3 b))
--   expand … : AStep G (p ++w (cons e3 b)) (p ++w (cons e1 (cons e2 b)))
-- ```
-- ⇒ 单一（不依赖 `d` 的）结论类型**不可能**，必须拆成两个函数 ✗
-- （报错原文：`The terms cons {…s2} _ _ and cons {…s1} (cEdge … s1) _ are not equal`。）
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
-- §4. `ASTep` 的三种铸型（各一行）
--
-- ⚠ `astStep-cast` 原先在 `T6AStepMap` §5d；该模块现由协作者改写并**删去**了它
-- （全库已无消费者，删除对其它模块无影响）⇒ 本模块就地补上，仍是一行 `refl` 级。
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

-- 沿**端点等式**整体铸型（**同一条** `e` 铸两侧 —— `ASTep` 要求两端点相同）
astStep-cast : ∀ {n : ℕ} {U V V' : T6Vec n} (e : V ≡ V')
               {p q : Walk (T6CayleySym n) U V} (s : AStep (T6CayleySym n) p q)
             → AStep (T6CayleySym n)
                     (subst (λ v → Walk (T6CayleySym n) U v) e p)
                     (subst (λ v → Walk (T6CayleySym n) U v) e q)
astStep-cast refl s = s

--------------------------------------------------------------------------------
-- §5. ★★★ 铸型工具：`subst` 合成 / `interpAt` 端点运输 / `cons` **依赖运输** / UIP
--
-- 四条全都是「对等式匹配到 `refl` 时两侧一起归约」的**一行**引理。
--------------------------------------------------------------------------------

-- ① `subst` 沿 `trans` 的合成（stdlib 无此件；对 `e1` 匹配到 `refl` 即两侧同时归约）
subst-trans : ∀ {A : Set} (P : A → Set) {x y z : A}
              (e1 : x ≡ y) (e2 : y ≡ z) (X : P x)
            → subst P (trans e1 e2) X ≡ subst P e2 (subst P e1 X)
subst-trans P refl e2 X = refl

-- ② ★ `interpAt` 沿**端点等式**的运输：源与终点**同时**变（这正是 `interpAt` 的好处：
--    族 `λ v → Walk G v (foldT v suff)` 只依赖**一个**变量 ⇒ 一行）
interpAt-subst : ∀ {n : ℕ} (suff : CWalk n) {a b : T6Vec n} (h : a ≡ b)
               → subst (λ v → Walk (T6CayleySym n) v (foldT v suff)) h
                       (interpAt a suff)
                 ≡ interpAt b suff
interpAt-subst suff refl = refl

-- ③ ★★★ 本模块的**关键**：`cons` 沿**中间顶点**的依赖运输
--
-- `cons e t` 的第二项 `t : Walk G z (foldT z suff)` 的**终点也依赖 z**
-- ⇒ `cons` 是依赖于中间顶点 `z` 的运算 ⇒ 沿 `k : z ≡ z'` 同时运输「边」与「尾走」。
-- 这一条把「码层的 `(cEdge X s3, q0)`」与「`toStep` 的 `(e3', b)`」接起来
-- —— 而 `subst-cons`（只运输终点、**不动边**）做不到这点。
cons-dtrans : ∀ {n : ℕ} (A : T6Vec n) (suff : CWalk n) {z z' : T6Vec n} (k : z ≡ z')
              (e : T6SymEdge A z) (t : Walk (T6CayleySym n) z (foldT z suff))
            → subst (Walk (T6CayleySym n) A) (cong (λ v → foldT v suff) k) (cons e t)
              ≡ cons (subst (T6SymEdge A) k e)
                     (subst (λ v → Walk (T6CayleySym n) v (foldT v suff)) k t)
cons-dtrans A suff refl e t = refl

-- ④ UIP（`T6Vec` 的相等可判定 ⇒ Hedberg ⇒ 同一对端点上的任意两条等式相等）
--    用途：目标侧的端点链走 `X_T`，源侧走 `Su`；两者都是 `W ≡ X_S` ⇒ 用 UIP 对齐。
T6Vec-UIP : ∀ {n : ℕ} {a b : T6Vec n} (p q : a ≡ b) → p ≡ q
T6Vec-UIP {n} p q = uip p q
  where
  open Decidable⇒UIP (DecEq-T6Vec {n}) renaming (≡-irrelevant to uip)

--------------------------------------------------------------------------------
-- §6a. 源侧：码层源走 ≡ `subst eSg` 形态（`interpC-walk'` + `interpAt-++-glue`）
--------------------------------------------------------------------------------

src-eq : ∀ {n : ℕ} (u : T6Vec n) (pref : CWalk n) (s1 s2 : CStep n) (suff : CWalk n)
       → subst (Walk (T6CayleySym n) u)
               (trans (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff)))
                      (sym (interpC-end u (pref ++ (s1 ∷ s2 ∷ suff)))))
               (interpAt u pref ++w interpAt (foldT u pref) (s1 ∷ s2 ∷ suff))
         ≡ proj₂ (interpC u (pref ++ (s1 ∷ s2 ∷ suff)))
src-eq {n} u pref s1 s2 suff =
  trans (subst-trans (Walk (T6CayleySym n) u)
                     (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff)))
                     (sym (interpC-end u (pref ++ (s1 ∷ s2 ∷ suff))))
                     (interpAt u pref ++w interpAt (foldT u pref) (s1 ∷ s2 ∷ suff)))
        (trans (cong (subst (Walk (T6CayleySym n) u)
                            (sym (interpC-end u (pref ++ (s1 ∷ s2 ∷ suff)))))
                     (sym (interpAt-++-glue u pref (s1 ∷ s2 ∷ suff))))
               (sym (interpC-walk' u (pref ++ (s1 ∷ s2 ∷ suff)))))

--------------------------------------------------------------------------------
-- §6b. 目标侧：`toStep` 的靶走（中间顶点 `Z`）≡ 码层靶走的端点复合运输
--
-- ## 五步链（每步都指向具体引理）
--
-- 记 `X = foldT u pref`、`Zc = ctarget X s3`、`Z = ctarget (ctarget X s1) s2`、
--   `p = interpAt u pref`、`q0 = interpAt Zc suff`、`b = interpAt Z suff`、
--   `e3 = cEdge X s3`、`e3' = subst (T6SymEdge X) h e3`、`hh = cong (foldT · suff) h`。
--
-- 1. `Xtgt ≡ subst P hh Xt` —— `stepE3-dtrans`（③+②）给出
--    `subst P hh (cons e3 q0) ≡ cons e3' b`，再用 `subst-++w` 提出前缀 `p`；
-- 2. `cong (subst P eSg)`；
-- 3. `subst-trans`（合成 `hh` 与 `eSg`）；
-- 4. `T6Vec-UIP`：`trans hh eSg` 与 `eWt = trans eTg (sym eS)` 都是 `W ≡ X_S` ⇒ 可换；
-- 5. `subst-trans` + 码层靶走归一（`interpAt-++-glue` + `interpC-walk'`）。
--------------------------------------------------------------------------------

tgt-eq : ∀ {n : ℕ} (u : T6Vec n) (d : ADir) (pref : CWalk n)
         (s1 s2 s3 : CStep n) (suff : CWalk n)
       → (h : ctarget (foldT u pref) s3 ≡ ctarget (ctarget (foldT u pref) s1) s2)
       → subst (Walk (T6CayleySym n) u)
               (trans (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff)))
                      (sym (interpC-end u (pref ++ (s1 ∷ s2 ∷ suff)))))
               (interpAt u pref ++w
                cons (subst (λ w → T6SymEdge (foldT u pref) w) h (cEdge (foldT u pref) s3))
                     (interpAt (ctarget (ctarget (foldT u pref) s1) s2) suff))
         ≡ subst (Walk (T6CayleySym n) u)
                 (sym (StepVertex→StepSide u (mkStep d pref s1 s2 s3 suff) h))
                 (proj₂ (interpC u (pref ++ (s3 ∷ suff))))
tgt-eq {n} u d pref s1 s2 s3 suff h = chain
  where

  P : T6Vec n → Set
  P = Walk (T6CayleySym n) u

  X : T6Vec n
  X = foldT u pref

  Zc : T6Vec n
  Zc = ctarget X s3

  Z : T6Vec n
  Z = ctarget (ctarget X s1) s2

  p : Walk (T6CayleySym n) u X
  p = interpAt u pref

  q0 : Walk (T6CayleySym n) Zc (foldT Zc suff)
  q0 = interpAt Zc suff

  b : Walk (T6CayleySym n) Z (foldT Z suff)
  b = interpAt Z suff

  e3 : T6SymEdge X Zc
  e3 = cEdge X s3

  e3' : T6SymEdge X Z
  e3' = subst (λ w → T6SymEdge X w) h e3

  hh : foldT Zc suff ≡ foldT Z suff
  hh = cong (λ v → foldT v suff) h

  -- `toStep` 的靶走形态（中间顶点 `Z`）
  Xtgt : Walk (T6CayleySym n) u (foldT Z suff)
  Xtgt = p ++w cons e3' b

  -- 码层靶走的中间形态（中间顶点 `Zc`）
  Xt : Walk (T6CayleySym n) u (foldT Zc suff)
  Xt = p ++w cons e3 q0

  eS0 : proj₁ (interpC u (pref ++ (s1 ∷ s2 ∷ suff)))
      ≡ foldT u (pref ++ (s1 ∷ s2 ∷ suff))
  eS0 = interpC-end u (pref ++ (s1 ∷ s2 ∷ suff))

  eSg : foldT Z suff ≡ proj₁ (interpC u (pref ++ (s1 ∷ s2 ∷ suff)))
  eSg = trans (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff))) (sym eS0)

  eT0 : proj₁ (interpC u (pref ++ (s3 ∷ suff)))
      ≡ foldT u (pref ++ (s3 ∷ suff))
  eT0 = interpC-end u (pref ++ (s3 ∷ suff))

  eTg : foldT Zc suff ≡ proj₁ (interpC u (pref ++ (s3 ∷ suff)))
  eTg = trans (sym (foldT-++ u pref (s3 ∷ suff))) (sym eT0)

  eS : proj₁ (interpC u (pref ++ (s1 ∷ s2 ∷ suff)))
     ≡ proj₁ (interpC u (pref ++ (s3 ∷ suff)))
  eS = StepVertex→StepSide u (mkStep d pref s1 s2 s3 suff) h

  eWt : foldT Zc suff ≡ proj₁ (interpC u (pref ++ (s1 ∷ s2 ∷ suff)))
  eWt = trans eTg (sym eS)

  -- ① `cons` 沿中间顶点的依赖运输（`h : Zc ≡ Z`）：边与尾走一起走
  stepE3-dtrans : subst (Walk (T6CayleySym n) X) hh (cons e3 q0) ≡ cons e3' b
  stepE3-dtrans =
    trans (cons-dtrans X suff h e3 q0) (cong (cons e3') (interpAt-subst suff h))

  -- ② 提出前缀 `p`：`subst P hh Xt ≡ Xtgt`（注意方向）
  stepA : Xtgt ≡ subst P hh Xt
  stepA = trans (sym (cong (λ q → p ++w q) stepE3-dtrans))
                (sym (subst-++w p hh (cons e3 q0)))

  -- ③ 码层靶走归一：`subst P eTg Xt ≡ tgtW`
  stepB : subst P eTg Xt ≡ proj₂ (interpC u (pref ++ (s3 ∷ suff)))
  stepB =
    trans (subst-trans P (sym (foldT-++ u pref (s3 ∷ suff))) (sym eT0) Xt)
          (trans (cong (subst P (sym eT0))
                       (sym (interpAt-++-glue u pref (s3 ∷ suff))))
                 (sym (interpC-walk' u (pref ++ (s3 ∷ suff)))))

  -- ④ 五步链**分段具名**（每段 `trans` 深度 ≤ 1，避免深嵌套；`where` 内须按依赖顺序排）
  chainAB : subst P eSg Xtgt ≡ subst P (trans hh eSg) Xt
  chainAB = trans (cong (subst P eSg) stepA) (sym (subst-trans P hh eSg Xt))

  chainABC : subst P eSg Xtgt ≡ subst P eWt Xt
  chainABC = trans chainAB
                   (cong (λ e → subst P e Xt) (T6Vec-UIP (trans hh eSg) eWt))

  chainABCD : subst P eSg Xtgt ≡ subst P (sym eS) (subst P eTg Xt)
  chainABCD = trans chainABC (subst-trans P eTg (sym eS) Xt)

  chain : subst P eSg Xtgt
        ≡ subst P (sym eS) (proj₂ (interpC u (pref ++ (s3 ∷ suff))))
  chain = trans chainABCD (cong (subst P (sym eS)) stepB)

--------------------------------------------------------------------------------
-- §7. ★★★ 主定理：`toStepCode`
--
-- ## 组装（三步）
--
-- 1. `astStep-cast eSg (toStep …)` —— **同一条**端点等式 `eSg` 铸**两侧**
--    （`toStep` 的两条走都在端点 `Z suff`…… 确切说 `foldT Z suff`）；
-- 2. `astStep-tgt (tgt-eq …)` —— 靶侧换成码层靶走（§6b）；
-- 3. `astStep-src (src-eq …)` —— 源侧换成码层源走（§6a）。
--
-- ## 负向对照（实测，证明「缺 `sym`」是**类型错误**而非风格问题）
--
-- 把 `sym (StepVertex→StepSide u c h)` 写成 `StepVertex→StepSide u c h` 时，
-- 报在**类型签名**行：
-- ```
--   error: [UnequalTerms] … when checking that the expression
--   StepVertex→StepSide u c h has type
--   proj₁ (interpC u (srcCode c)) ≡ proj₁ (interpC u (tgtCode c))
-- ```
-- —— `subst` 需要的是**反向**的等式（被运输项落在 `P y` 侧）。
--------------------------------------------------------------------------------

toStepCode : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) (h : StepVertex u c)
           → AStep (T6CayleySym n)
                   (proj₂ (interpC u (srcCode c)))
                   (subst (Walk (T6CayleySym n) u) (sym (StepVertex→StepSide u c h))
                          (proj₂ (interpC u (tgtCode c))))
toStepCode u (mkStep d pref s1 s2 s3 suff) h =
  astStep-src (src-eq u pref s1 s2 suff)
    (astStep-tgt (tgt-eq u d pref s1 s2 s3 suff h)
      (astStep-cast (trans (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff)))
                           (sym (interpC-end u (pref ++ (s1 ∷ s2 ∷ suff)))))
                    (toStep u pref s1 s2 s3 suff h)))

--------------------------------------------------------------------------------
-- §7c. 码的**可实现性判定**（`T6AStepMap` 改写时删掉了 `decStepVertex`，全库已无此件）
--
-- `StepVertex` 只是两个 `foldT` 顶点之间的等式，而 `T6Vec n` 的相等**可判定**
-- ⇒ 直接算，不需要 uip（与 `T6AStepMap.decStepSide` 同一手法）。
-- 有了它，`toStepCode` 的**前提可以算**：`decStepCode u c` 给出「这个码在 `u` 处能不能走一步」。
--------------------------------------------------------------------------------

decStepCode : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) → Dec (StepVertex u c)
decStepCode u (mkStep d pref s1 s2 s3 suff) =
  DecEq-T6Vec (ctarget (foldT u pref) s3)
              (ctarget (ctarget (foldT u pref) s1) s2)

--------------------------------------------------------------------------------
-- §7b. ★★ `expand` 方向 + **按 `ADir` 分派**（在 `AHomotopy` 层，不在 `ASTep` 层）
--
-- ## 为什么分派只能在 `AHomotopy` 层做
--
-- §3 记过：`slide` 与 `expand` 的**结论类型相反** ⇒ 单一函数（不依赖 `d` 的结论）不可能。
-- 但 `AHomotopy` 是**对称闭包**（构造子 `symm`）⇒ 两个方向**同型**
-- （都是 `srcW → tgtW'`）⇒ 分派在 `AHomotopy` 层完全合法 ✓。
-- 这是「换载体」手法的又一例：**换到对称闭包，双向就统一了**。
--------------------------------------------------------------------------------

-- `expand` 方向（`toStepCode` 的镜像）：`tgtW' → srcW`
toStepCodeExpand : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) (h : StepVertex u c)
                 → AStep (T6CayleySym n)
                         (subst (Walk (T6CayleySym n) u) (sym (StepVertex→StepSide u c h))
                                (proj₂ (interpC u (tgtCode c))))
                         (proj₂ (interpC u (srcCode c)))
toStepCodeExpand u (mkStep d pref s1 s2 s3 suff) h =
  astStep-src (tgt-eq u d pref s1 s2 s3 suff h)
    (astStep-tgt (src-eq u pref s1 s2 suff)
      (astStep-cast (trans (sym (foldT-++ u pref (s1 ∷ s2 ∷ suff)))
                           (sym (interpC-end u (pref ++ (s1 ∷ s2 ∷ suff)))))
                    (toStepExpand u pref s1 s2 s3 suff h)))

-- 码 → A-同伦（`slide` 方向）
toAHomotopy : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) (h : StepVertex u c)
            → AHomotopy (T6CayleySym n)
                        (proj₂ (interpC u (srcCode c)))
                        (subst (Walk (T6CayleySym n) u) (sym (StepVertex→StepSide u c h))
                               (proj₂ (interpC u (tgtCode c))))
toAHomotopy u c h = AStep⊆AH (toStepCode u c h)

-- ★ 按码里带的 `ADir` 分派（`AHomotopy` 层；`ASTep` 层做不到）
toAHomotopyDir : ∀ {n : ℕ} (u : T6Vec n) (c : StepCode n) (h : StepVertex u c)
                 (e : ADir)
               → AHomotopy (T6CayleySym n)
                           (proj₂ (interpC u (srcCode c)))
                           (subst (Walk (T6CayleySym n) u) (sym (StepVertex→StepSide u c h))
                                  (proj₂ (interpC u (tgtCode c))))
toAHomotopyDir u c h dslide  = toAHomotopy u c h
toAHomotopyDir u c h dexpand = AH-symm (AStep⊆AH (toStepCodeExpand u c h))

--------------------------------------------------------------------------------
-- §8. 对抗验证（纪律 §6）：在**具体点**上实例化整条链
--
-- 取 `n = 1`、前缀/后缀都空、三角形 `+e₀`、`+e₀`、`-e₀`（与 `T6CayleyInterp` §7 同一点）：
-- `-e₀` 从 `x` 到 `x+2e₀`，而 `+e₀;+e₀` 也到 `x+2e₀` ⇒ 侧条件**两边算到同一个顶点**。
--
-- 三样都必须是**计算**（不是「论证」）：
--   ① 侧条件在具体点成立（`refl`）；② 码的具体值；③ 整条 `toStepCode` **有类型**
--   ⇒ 它产出一个**真实** `ASTep` 值（不是空洞项）。
--------------------------------------------------------------------------------

-- ⚠ x1 复用 T6CayleyInterp（不重造）

code1 : StepCode 1
code1 = mkStep dslide [] (cplus zero) (cplus zero) (cminus zero) []

-- ① 侧条件（三角形闭合）—— `refl`
side-code-1 : StepVertex x1 code1
side-code-1 = refl

-- ② ★ 整条 `toStepCode` 在具体点**有类型**（因此产出真实的 `ASTep` 值）
step-code-1 : AStep (T6CayleySym 1)
             (proj₂ (interpC x1 (srcCode code1)))
             (subst (Walk (T6CayleySym 1) x1) (sym (StepVertex→StepSide x1 code1 side-code-1))
                    (proj₂ (interpC x1 (tgtCode code1))))
step-code-1 = toStepCode x1 code1 side-code-1

-- ③ `expand` 方向在具体点同样**有类型**
step-code-1-expand : AStep (T6CayleySym 1)
                      (subst (Walk (T6CayleySym 1) x1) (sym (StepVertex→StepSide x1 code1 side-code-1))
                             (proj₂ (interpC x1 (tgtCode code1))))
                      (proj₂ (interpC x1 (srcCode code1)))
step-code-1-expand = toStepCodeExpand x1 code1 side-code-1

-- ④ 分派（`dexpand` 走 `symm`）在具体点**有类型**
ah-1 : AHomotopy (T6CayleySym 1)
                 (proj₂ (interpC x1 (srcCode code1)))
                 (subst (Walk (T6CayleySym 1) x1) (sym (StepVertex→StepSide x1 code1 side-code-1))
                        (proj₂ (interpC x1 (tgtCode code1))))
ah-1 = toAHomotopyDir x1 code1 side-code-1 dexpand

--------------------------------------------------------------------------------
-- §9. ★ 负向控制（纪律 §0.75 第②档）：`decStepCode` 的 `no` 分支**可达**
--
-- 只证「`yes` 分支有值」（§8）是不够的 —— 那只能说明判官会说「是」。
-- 这里证明某码在该点**确实不可实现**（侧条件假），于是判官**会说「不」**。
--
-- 取同上一点 `x1`，但第三步换成 `cplus zero`（同向而非互逆）：
-- 侧条件退化成 `updAt 0 x1 ≡ updAt 0 (updAt 0 x1)`，
-- 即 `[1] ≡ [2]`（`succF3` 前两个具体值）⇒ 由 `Fin` 构造子冲突**不成立**。
--------------------------------------------------------------------------------

-- 同向第三步的码（侧条件**假**）
code0 : StepCode 1
code0 = mkStep dslide [] (cplus zero) (cplus zero) (cplus zero) []

-- `succF3` 的两个具体值不同：`0 ↦ 1`、`1 ↦ 2`（`Fin` 构造子冲突，空模式即闭合）
succF3-0≢2 : succF3 Fin.zero ≢ succF3 (succF3 Fin.zero)
succF3-0≢2 = λ ()

-- ★ `decStepCode` 的 `no` 分支可达：该码在 `x1` 处**不可实现**
noStepVertex : StepVertex x1 code0 → ⊥
noStepVertex e = succF3-0≢2 (cong head e)

-- ★ 判定器**确实在算**（不是 stuck 项）：正例上 `decStepCode` 归约到 `yes`
decStepCode-yes : decStepCode x1 code1 ≡ yes side-code-1
decStepCode-yes = refl

-- ★ 负例上归约到 `no`（`Dec` 的两个分支都真的在算）
decStepCode-no : decStepCode x1 code0 ≡ no noStepVertex
decStepCode-no = refl
