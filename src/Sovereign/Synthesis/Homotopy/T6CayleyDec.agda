{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Homotopy.T6CayleyDec
--
-- **证明无分量的可判定性原语** —— 路 (a3) 的第一级台阶
--
-- ## 为什么需要这一件
--
-- 台账 `PN.B4.pi2d-free-group-boundary` 记了一个**真边界**：
-- 「一般图上 `π₂ᵈ⁺` 的分类」在 `--without-K` 下**不可做** ——
-- 因为它要 `DecEq (ASTep)`，而这条链的最后一环 `edge x y` 常是
-- **带相等证明分量的 `Σ`**，比较证明需 `uip`（`--cubical` ⇒ `--without-K` ⇒ 不可用）。
--
-- **出路**：把「判定」放在**无证明分量**的层上。
-- 本模块给这个层的第一级台阶：
--
-- | 原语 | 类型 | 说明 |
-- |---|---|---|
-- | `DecEq-T6Vec` | `(u v : T6Vec n) → Dec (u ≡ v)` | `Vec (Fin 3) n` 的可判定相等（`Fin 3` 可判定 + `Vec` 逐位比较）|
-- | `decAt` | `(j : Fin n) (x y : T6Vec n) → Dec (y ≡ updAt j x)` | ★ **判定「沿方向 `+e_j` 是否有边 `x → y`」** |
-- | `decAt2` | 同上，但方向是 `−e_j`（即 `updAt j (updAt j ·)`）| |
--
-- **关键**：这些都是**判定「陈述」**（`y ≡ updAt j x`），
-- 而**不是**判定「`T6SymEdge` 的两个**元素**是否相等」——
-- 后者才需要比较证明分量 ✗。前者的结果类型是 `Dec (y ≡ updAt j x)`，
-- 其中 `y`、`updAt j x` 都是 `Vec (Fin 3) n`（**无证明分量**）✓
--
-- ## 核心原则
--   · 0 postulate / 0 hole；零 Cubical
--   · 全部复用 stdlib（`Data.Vec.Properties.≡-dec` + `Fin._≟_`）

module Sovereign.Synthesis.Homotopy.T6CayleyDec where

open import Data.Nat using (ℕ; _+_; zero; suc)
open import Data.Maybe using (just; nothing; Maybe)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Vec using (Vec) renaming ([] to []ᵥ; _∷_ to _∷ᵥ_)
open import Data.Fin using (Fin)
import Data.Fin as Fin
import Data.Fin as Fin
open import Data.Vec.Properties using (≡-dec)
open import Data.List using (List; []; _∷_; length; map)
open import Data.List.Properties using (length-map)
open import Data.Nat.Properties using (+-suc)
open import Function using (_∘_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans) using (_≡_; refl; cong; sym; trans)

open import Sovereign.Synthesis.Homotopy.T6CayleyVec using (T6Vec; updAt)
open import Sovereign.Synthesis.Homotopy.T6CayleySym using (T6SymEdge)

--------------------------------------------------------------------------------
-- §1. `T6Vec n = Vec (Fin 3) n` 的可判定相等
--------------------------------------------------------------------------------

DecEq-T6Vec : ∀ {n : ℕ} (u v : T6Vec n) → Dec (u ≡ v)
DecEq-T6Vec = ≡-dec (Fin._≟_)

--------------------------------------------------------------------------------
-- §2. ★ 方向判定原语：沿 `+e_j` / `−e_j` 是否有边
--
-- 这两个是**归约**真正需要的：判断「第 j 个坐标推进后是不是这个顶点」。
-- 注意它们判定的是**语句**，不涉及任何证明分量 ✓
--------------------------------------------------------------------------------

decAt : ∀ {n : ℕ} (j : Fin n) (x y : T6Vec n) → Dec (y ≡ updAt j x)
decAt j x y = DecEq-T6Vec y (updAt j x)

decAt2 : ∀ {n : ℕ} (j : Fin n) (x y : T6Vec n) → Dec (y ≡ updAt j (updAt j x))
decAt2 j x y = DecEq-T6Vec y (updAt j (updAt j x))

--------------------------------------------------------------------------------
-- §3. ⬜ 下一级台阶（未做，判据明确）
--
-- 要用上面两个原语做**归约**，还差：
--
-- ① **邻居表**：`neighbours : T6Vec n → List (T6Vec n)`（显式枚举 `n` 坐标 × `±` 两向）
-- ② **对应定理（两向）**：
--      `T6SymEdge x y → y ∈ neighbours x`
--      `y ∈ neighbours x → T6SymEdge x y`
--    ← 第二步需要「从成员关系找回 `j`」，即 `List` 的索引搜索（stdlib 的
--      `Data.List.Membership` 或自写 `find`）。
-- ③ 在**无证明分量**的 `List (T6Vec n)` 上做 `reduce`（`&&`-链 + `fuel`）。
--
-- ⇒ 这三步都在 `--without-K` 下**可做**（因为 `Vec (Fin 3) n` 相等可判定），
--   而「一般图」的版本**不可做** —— 这就是台账记的那个真边界。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §4. ★★ 带**见证**的边查找：`Maybe (T6SymEdge x y)`
--
-- ⚠ 为什么用 `Maybe` 而**不用** `Dec`：
--   `Dec` 的 `no` 分支要**证明不存在**，而扫描到 `[]` 只意味着「枚举完了」，
--   并不在类型上意味着 `Fin n` 为空 ⇒ 需要额外的**穷尽性引理**
--   （`∀ j → j ∈ allFinD n`）才能闭 `no`。那是另一步。
--   `Maybe` 的 `nothing` **无需任何证明** ✓ 且对归约**操作上足够**
--   （有边就拿到见证，没边就停）。
--
-- ⚠ 与「判定两个 `T6SymEdge` 元素是否相等」的区别（关键）：
--   本函数**构造**见证 —— 容易；判定 `e ≡ e'` 要**比较证明分量** ⇒ 需 uip，不可用。
--------------------------------------------------------------------------------

-- 自带的索引枚举（不依赖 stdlib 的 `allFin` —— 本 stdlib 版本的 `Data.Fin`/`Data.Fin.Base` 都不导出它）
allFinD : (n : ℕ) → List (Fin n)
allFinD zero    = []
allFinD (suc n) = Fin.zero ∷ map Fin.suc (allFinD n)

findEdge : ∀ {n : ℕ} (x y : T6Vec n) → Maybe (T6SymEdge x y)
findEdge {n} x y = scan (allFinD n)
  where
    scan : List (Fin n) → Maybe (T6SymEdge x y)
    scan []        = nothing
    scan (j ∷ js) with decAt j x y
    ... | yes p = just (inj₁ (j , p))
    ... | no  _ with decAt2 j x y
    ...   | yes q = just (inj₂ (j , q))
    ...   | no  _ = scan js

--------------------------------------------------------------------------------
-- §5. ★ 穷尽性引理：每个 `Fin n` 都在 `allFinD n` 里
--
-- 这是 `Dec` 版本的**最后一块前提**：
-- 扫描到 `[]` 时，要靠它把「枚举完了」转成「真的没有」。
--
-- 自带 `∈-map'`（不复用 stdlib 的 `∈-map`，避免签名版本差）。
--------------------------------------------------------------------------------

∈-map' : ∀ {A B : Set} {f : A → B} {x : A} {xs : List A}
       → x ∈ xs → f x ∈ map f xs
∈-map' (here refl) = here refl
∈-map' (there pf)  = there (∈-map' pf)

∈-allFinD : ∀ {n : ℕ} (j : Fin n) → j ∈ allFinD n
∈-allFinD {suc n} Fin.zero    = here refl
∈-allFinD {suc n} (Fin.suc j) = there (∈-map' {f = Fin.suc} (∈-allFinD j))

--------------------------------------------------------------------------------
-- §6. ✅ `Dec` 版的台阶**已在 §8 完成**（本节原标「⬜ 下一级台阶」已过期）
--
-- `findEdgeDec : (x y : T6Vec n) → Dec (T6SymEdge x y)` 见 §8；
-- 可靠性 `findEdgeDec-sound` / 完备性 `findEdgeDec-complete` 见 `T6CayleyDecSound`。
--
-- 原计划文字（保留作设计记录）：有了 §5，就可以把 `findEdge` 升级成 `Dec` 版：
--   `scan` 必须**携带失败信息**（`∀ j∈js → ¬ (y ≡ updAt j x) × ¬ (y ≡ updAt j (updAt j x))`），
--   在 `[]` 处用 `∈-allFinD` 把任意给出的 `T6SymEdge` 的索引代入，得到矛盾。
-- 然后才能在 `List (T6Vec n)`（**无证明分量**）上做 `reduce`（fuel），
-- 最后才是 `Ω3Walk⁺` 与 `reduce` 的双方对应（分类定理）。
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- §7. ★★ `findEdge` 的**计算行为**（具体点对抗验证，纪律 §6）
--
-- `findEdge` 是 `Maybe` 版：它不证明「没有边」，所以**必须**验证它在具体点上
-- 真的在算（而不是停在某个 stuck 项上）。两个方向各取一点，都是 `refl`：
--   · 不是边 ⇒ `nothing`（扫描走到底）
--   · 是边   ⇒ `just (inj₁ (zero , refl))`（拿到见证）
--------------------------------------------------------------------------------

vec0 : T6Vec 1
vec0 = Fin.zero ∷ᵥ []ᵥ

-- ① 非边：`(0)` 不是 `(0)` 的 ±e₀ 邻居 ⇒ `nothing`
findEdge-nothing : findEdge vec0 vec0 ≡ nothing
findEdge-nothing = refl

-- ② 是边：`+e₀` 的邻居 ⇒ `just`，见证 `inj₁ (zero , refl)`
findEdge-just : findEdge vec0 (updAt Fin.zero vec0)
              ≡ just (inj₁ (Fin.zero , refl))
findEdge-just = refl

--------------------------------------------------------------------------------
-- §8. ★★★ `findEdge` 的 **`Dec` 版**（§6 点名的下一级台阶）
--
-- `Maybe` 版的 `nothing` 不携带任何信息；这里用 §5 的穷尽性引理把它补成真判定：
-- 扫描时携带不变式「已查过的索引（`∈ allFinD n` 且 `∉ rest`）两段式谓词都失败」，
-- 扫到 `[]` 时任一见证 `j` 都有 `j ∈ allFinD n`、且 `j ∉ []` ⇒ 与不变式矛盾 ✓
-- ⇒ `T6SymEdge x y` 的**存在性可判定**，这是「在无证明分量的 `List (T6Vec n)` 上做
--   `reduce`」所缺的那块（`Dec` 的 `no` 现在有底了）。
--------------------------------------------------------------------------------

P1 : ∀ {n : ℕ} (x y : T6Vec n) (j : Fin n) → Set
P1 x y j = y ≡ updAt j x

P2 : ∀ {n : ℕ} (x y : T6Vec n) (j : Fin n) → Set
P2 x y j = y ≡ updAt j (updAt j x)

_∉_ : ∀ {A : Set} → A → List A → Set
x ∉ xs = x ∈ xs → ⊥

∉-cons : ∀ {A : Set} {x y : A} {xs : List A} → ¬ (x ≡ y) → x ∉ xs → x ∉ (y ∷ xs)
∉-cons x≢y x∉xs (here refl) = x≢y refl
∉-cons x≢y x∉xs (there m)   = x∉xs m

-- 扫描主体（提到顶层，便于对它做归纳）
scanDec : ∀ {n : ℕ} (x y : T6Vec n) (rest : List (Fin n))
        → (∀ j → j ∈ allFinD n → j ∉ rest → (¬ P1 x y j) × (¬ P2 x y j))
        → Dec (T6SymEdge x y)
scanDec x y [] inv =
  no λ { (inj₁ (j , p)) → proj₁ (inv j (∈-allFinD j) (λ ())) p
       ; (inj₂ (j , q)) → proj₂ (inv j (∈-allFinD j) (λ ())) q }
scanDec {n} x y (k ∷ ks) inv with decAt k x y | decAt2 k x y
... | yes p  | _      = yes (inj₁ (k , p))
... | no ¬p  | yes q  = yes (inj₂ (k , q))
... | no ¬p  | no ¬q  = scanDec x y ks inv'
  where
    inv' : ∀ j → j ∈ allFinD n → j ∉ ks → (¬ P1 x y j) × (¬ P2 x y j)
    inv' j j∈all j∉ks with j Fin.≟ k
    ... | yes refl = ¬p , ¬q
    ... | no  j≢k  = inv j j∈all (∉-cons j≢k j∉ks)

findEdgeDec : ∀ {n : ℕ} (x y : T6Vec n) → Dec (T6SymEdge x y)
findEdgeDec {n} x y = scanDec x y (allFinD n) inv0
  where
    inv0 : ∀ j → j ∈ allFinD n → j ∉ allFinD n → (¬ P1 x y j) × (¬ P2 x y j)
    inv0 j _ j∉ = ⊥-elim (j∉ (∈-allFinD j))

--------------------------------------------------------------------------------
-- 完备性（**只要存在边，扫描一定说 `yes`**）的证明放在 `T6CayleyDecSound` §5 ——
-- 那里已经 import 了 `TSet`（`Dec` 的反射型），避免本模块反向依赖 `T6AStepCode2` 造成层序倒置。
--------------------------------------------------------------------------------

-- 可靠性（`findEdgeDec-sound`）放在 `T6CayleyDecSound`（那里已 import `TSet`，
-- 避免本模块反向依赖 `T6AStepCode2` 造成层序倒置）。

--------------------------------------------------------------------------------
-- §9. ★★★ 邻居表与**边 ↔ 成员**的双向对应（§3 的 ①②）
--
-- `neighbours x` 显式枚举 `n` 个坐标 × 两个方向（`+e_j` / `−e_j`，后者是两次 `updAt`）。
-- 双向对应：`T6SymEdge x y ⇔ y ∈ neighbours x` —— 这是把 `findEdge` 换成「查表」、
-- 进而在**无证明分量**的 `List (T6Vec n)` 上做 `reduce` 的前提。
--------------------------------------------------------------------------------

nbrsFrom : ∀ {n : ℕ} (x : T6Vec n) (js : List (Fin n)) → List (T6Vec n)
nbrsFrom x []       = []
nbrsFrom x (j ∷ js) = updAt j x ∷ updAt j (updAt j x) ∷ nbrsFrom x js

neighbours : ∀ {n : ℕ} (x : T6Vec n) → List (T6Vec n)
neighbours {n} x = nbrsFrom x (allFinD n)

-- ① 表中每个元素**都是**邻居
nbrsFrom-sound : ∀ {n : ℕ} (x : T6Vec n) (js : List (Fin n)) {y : T6Vec n}
               → y ∈ nbrsFrom x js → T6SymEdge x y
nbrsFrom-sound x (j ∷ js) (here refl)         = inj₁ (j , refl)
nbrsFrom-sound x (j ∷ js) (there (here refl)) = inj₂ (j , refl)
nbrsFrom-sound x (j ∷ js) (there (there m))   = nbrsFrom-sound x js m

-- ② 每个邻居**都在**表里（给定索引与方向）
nbrsFrom-complete : ∀ {n : ℕ} (x : T6Vec n) (js : List (Fin n)) (j : Fin n)
                  → j ∈ js → (y : T6Vec n)
                  → (y ≡ updAt j x) ⊎ (y ≡ updAt j (updAt j x))
                  → y ∈ nbrsFrom x js
nbrsFrom-complete x (k ∷ ks) j (here refl)  y (inj₁ p) = here p
nbrsFrom-complete x (k ∷ ks) j (here refl)  y (inj₂ q) = there (here q)
nbrsFrom-complete x (k ∷ ks) j (there m)    y wit     =
  there (there (nbrsFrom-complete x ks j m y wit))

neighbours-sound : ∀ {n : ℕ} (x : T6Vec n) {y : T6Vec n}
                 → y ∈ neighbours x → T6SymEdge x y
neighbours-sound {n} x = nbrsFrom-sound x (allFinD n)

neighbours-complete : ∀ {n : ℕ} (x : T6Vec n) {y : T6Vec n}
                    → T6SymEdge x y → y ∈ neighbours x
neighbours-complete {n} x (inj₁ (j , p)) =
  nbrsFrom-complete x (allFinD n) j (∈-allFinD j) _ (inj₁ p)
neighbours-complete {n} x (inj₂ (j , q)) =
  nbrsFrom-complete x (allFinD n) j (∈-allFinD j) _ (inj₂ q)
-- 计算验证：`n = 1` 的邻居表恰是 `[+e₀, −e₀]`（两个元素），且 `+e₀` 确实在表里
nx1 : T6Vec 1
nx1 = Fin.zero ∷ᵥ []ᵥ

nbr-1-len : length (neighbours nx1) ≡ 2
nbr-1-len = refl

nbr-1-head : updAt Fin.zero nx1 ∈ neighbours nx1
nbr-1-head = here refl
-- 表长：`neighbours x` 恰有 `n + n` 个条目（与「双向对应」合起来给出表的完整刻画）
length-nbrsFrom : ∀ {n : ℕ} (x : T6Vec n) (js : List (Fin n))
                → length (nbrsFrom x js) ≡ length js + length js
length-nbrsFrom x []       = refl
length-nbrsFrom x (j ∷ js) =
  trans (cong (suc ∘ suc) (length-nbrsFrom x js))
        (sym (cong suc (+-suc (length js) (length js))))

length-allFinD : (n : ℕ) → length (allFinD n) ≡ n
length-allFinD zero    = refl
length-allFinD (suc n) = cong suc (trans (length-map Fin.suc (allFinD n)) (length-allFinD n))

length-neighbours : ∀ {n : ℕ} (x : T6Vec n) → length (neighbours x) ≡ n + n
length-neighbours {n} x = trans (length-nbrsFrom x (allFinD n))
                                (cong (λ k → k + k) (length-allFinD n))
-- ⚠ **边界（如实标注）**：表长 `n + n` **不蕴含**「表内无重复」——
--   `Nodup (neighbours x)` **未证**（需 `updAt` 的单射性/不同坐标不相交等引理）。
--   若要断言「无冗余」，必须补 `Nodup`；在此之前只能说**条目数恰为 `n + n`**。
