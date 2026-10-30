{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.Tableau-Clauses
-- tableau 的子句族（原子层，**不含语义**）—— 里程碑 M3c 闸门 G3
--
-- 【本件做什么】把 tableau 的子句族写成**具体的 `List (List (ALit A))`**：每格
-- 「恰好一个符号」、每刻「恰好一个（状态, 头位置计数）」、一步转移、初始格局、
-- 终止格局。本件**只给形状**：满足性 ⟹ 运行的论证（G4/G5）在 `Tableau-Sem.agda`，
-- 本件不声称任何语义定理。
--
-- 【原子类型（2026-10-30 裁决 (a)）】状态原子带上头的**绝对位置**：
--   `atSt t q p`  ——  p = `|left|`（头的绝对位置；就是机器层 `left` 的长度）
--   `atSym i`     ——  符号格，`i` 是 G2 池号（`(时刻, 偏移, 符号)` 已压平）
-- 为什么必须带 `p`（决策书 `docs/decisions/M3c-C4-左边界分叉-2026-10-30.md`）：
-- 机器层 `leftLof` 的左空/左非空两支产出**不同**格局（`TuringMachine.agda:59-61`），
-- 而「左带为空」⟺ `|left| = 0` —— 是计数器，相对窗口看不见。把 `p` 放进状态原子，
-- 「左空 vs 左非空」就成了**局部可判**（`p` 是否 `fzero`），于是 C4 三支都能写成
-- 常量宽度子句，且**不动冻结的 M2**。
--
-- 【`p` 的递推（与机器层严格对应）】
--   R            : `p′ = suc p`（封顶于 T，见 `pSuc`）
--   L, p = 0     : `p′ = 0`，头不动，w′ 写在新 `tH`
--   L, p = suc n : `p′ = n`，头左移，w′ 写在新 `tR 0`
--   `|left| ≤ t ≤ T` ⟹ `Fin (suc T)` 足够（初始 p = 0，每步至多 +1）。
--
-- 【C3 去哪了】计划原表 C3「头 oneHot」在相对行方案下为空（每行头恒为 `tH`）；
-- 裁决 §3.3 把它改述为「`p` 的递推一致性」——而该内容正是 C4 三条子句的**目标文字**
-- （`atSt (fsuc t) q′ p′`），不需要独立族。剩下的「`p ≤ t` 裁剪」是规模优化
-- （裁决 §3.4），记为 C3′，不影响正确性，暂不做。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.Tableau-Clauses where

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; z≤n; s≤s⁻¹)
open import Data.Nat.Properties using (≤-trans; m≤m+n)
open import Data.Fin using (Fin; toℕ; fromℕ; inject₁)
  renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_; map; concat; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Algebra.Complexity.SATMember using (Sign; σ₊; σ₋)
open import Sovereign.Algebra.Complexity.Tableau
  using (ALit; TEnv; oneHot; satAFormula)
open import Sovereign.Algebra.Complexity.Tableau-Tape
  using (TOff; tH; tL; tR; InOff)
open import Sovereign.Algebra.Complexity.Tableau-Pool using (poolSize; poolEnc)
open import Sovereign.Algebra.Automata.TuringMachine using (Dir; L; R)

-- ────────────────────────────────────────────────────────────────────
-- §0 枚举件与原子类型〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- `Fin n` 的全枚举（stdlib 只有 Vec 形态的 `tabulate`）
allFin : (n : ℕ) → List (Fin n)
allFin zero    = []
allFin (suc n) = fzero ∷ map fsuc (allFin n)

-- 取表头（带默认值；核对层要看首条子句的形状）
listHead : ∀ {A : Set} → A → List A → A
listHead d []      = d
listHead _ (x ∷ _) = x

-- `Fin (suc n)` 的取值界：`toℕ k ≤ n`
fin-le : ∀ {n : ℕ} (k : Fin (suc n)) → toℕ k ≤ n
fin-le k = s≤s⁻¹ (toℕ<n k)

-- 带界内性见证的偏移：`TOff` 不是 `Fin`，无法无见证枚举；把见证放进 Σ 里，
-- 下游取用时不必再构造证明。
OffW : (len t : ℕ) → Set
OffW len t = Σ TOff (InOff len t)

-- 时刻 t 的窗口全枚举：头格 + 左 k ≤ t + 右 k ≤ len + t + t
allOffW : (len t : ℕ) → List (OffW len t)
allOffW len t =
  (tH , tt)
  ∷ map (λ k → tL (toℕ k) , fin-le k) (allFin (suc t))
  ++ map (λ k → tR (toℕ k) , fin-le k) (allFin (suc (len + t + t)))

-- `p` 的后继（封顶于 T），语义 `min (p+1) T`。封顶支在实际运行里不可达
-- （`p ≤ t < T` 时不封顶），其子句被 C2 的 oneHot 逼成空真。
pSuc : ∀ (T : ℕ) → Fin (suc T) → Fin (suc T)
pSuc zero    p        = p
pSuc (suc T) fzero    = fsuc fzero
pSuc (suc T) (fsuc p) = fsuc (pSuc T p)

-- 原子：符号格（池号）+ 状态格（时刻 · 状态 · |left|）
data TabAtom (len T Q V : ℕ) : Set where
  atSym : Fin (poolSize len T V) → TabAtom len T Q V
  atSt  : Fin (suc T) → Fin Q → Fin (suc T) → TabAtom len T Q V

-- 蕴涵子句：两条负文字（前提）+ 一条正文字（结论）
imp : ∀ {A : Set} (u v w : A) → List (ALit A)
imp u v w = (σ₋ , u) ∷ ((σ₋ , v) ∷ ((σ₊ , w) ∷ []))

-- ────────────────────────────────────────────────────────────────────
-- §1 C1：每格「恰好一个符号」
-- ────────────────────────────────────────────────────────────────────
-- 与 M3a 的 `oneHot` 直接对接：符号族 = 池号列表；`oneHot` 给「至少一个」（长子句）
-- + 「至多一个」（成对 `¬u ∨ ¬v`）。三值语义下后者强制未选中者取 T₂。

symCells : ∀ (len T Q V : ℕ) (t : Fin (suc T)) (o : TOff) (h : InOff len (toℕ t) o)
         → List (TabAtom len T Q V)
symCells len T Q V t o h = map (λ a → atSym (poolEnc len T V t o h a)) (allFin V)

symOneHot : ∀ (len T Q V : ℕ) (t : Fin (suc T)) (o : TOff) (h : InOff len (toℕ t) o)
          → List (List (ALit (TabAtom len T Q V)))
symOneHot len T Q V t o h = oneHot (symCells len T Q V t o h)

-- ────────────────────────────────────────────────────────────────────
-- §2 C2：每刻「恰好一个 (状态, |left|)」
-- ────────────────────────────────────────────────────────────────────

stCells : ∀ (len T Q V : ℕ) (t : Fin (suc T)) → List (TabAtom len T Q V)
stCells len T Q V t =
  concat (map (λ q → map (λ p → atSt t q p) (allFin (suc T))) (allFin Q))

stOneHot : ∀ (len T Q V : ℕ) (t : Fin (suc T))
         → List (List (ALit (TabAtom len T Q V)))
stOneHot len T Q V t = oneHot (stCells len T Q V t)

-- ────────────────────────────────────────────────────────────────────
-- §3 C4：一步转移（三支；⇒ 方向，唯一性由目标行的 C2 oneHot 收口）
-- ────────────────────────────────────────────────────────────────────
-- 每支 2 条子句，形状 `¬St(t,s,p) ∨ ¬Sym(t,tH,a) ∨ <结论>`：
--   · 结论一：`St(t+1, q′, p′)` —— 状态与位置计数一步到位（裁决 §3.3 的「p 递推」）
--   · 结论二：写入符号落在哪个**新**偏移
--       R            → 新 `tL 0`（旧头格；`tShiftR tH = tL 0`）
--       L, p = 0     → 新 `tH`（头不动；`tShiftLN tH = tR 0` 是**旧头符号**的去处）
--       L, p = suc n → 新 `tR 0`（旧头格；`tShiftL tH = tR 1` 同理是旧头符号）
-- 其余格子由 C5（非头不变）按同一条平移原语搬运。

headSym : ∀ (len T Q V : ℕ) (t : Fin (suc T)) (a : Fin V) → TabAtom len T Q V
headSym len T Q V t a = atSym (poolEnc len T V t tH tt a)

transClauses : ∀ (len T Q V : ℕ) (δ : Fin Q → Fin V → Fin Q × Fin V × Dir)
                 (t : Fin T) (s : Fin Q) (a : Fin V) (p : Fin (suc T))
             → List (List (ALit (TabAtom len T Q V)))
transClauses len T Q V δ t s a p with δ s a
... | (q′ , w′ , R) =
  imp (atSt (inject₁ t) s p) (headSym len T Q V (inject₁ t) a)
      (atSt (fsuc t) q′ (pSuc T p))
  ∷ imp (atSt (inject₁ t) s p) (headSym len T Q V (inject₁ t) a)
        (atSym (poolEnc len T V (fsuc t) (tL zero) z≤n w′))
  ∷ []
... | (q′ , w′ , L) with p
...   | fzero =
  imp (atSt (inject₁ t) s fzero) (headSym len T Q V (inject₁ t) a)
      (atSt (fsuc t) q′ fzero)
  ∷ imp (atSt (inject₁ t) s fzero) (headSym len T Q V (inject₁ t) a)
        (atSym (poolEnc len T V (fsuc t) tH tt w′))
  ∷ []
...   | fsuc n =
  imp (atSt (inject₁ t) s (fsuc n)) (headSym len T Q V (inject₁ t) a)
      (atSt (fsuc t) q′ (inject₁ n))
  ∷ imp (atSt (inject₁ t) s (fsuc n)) (headSym len T Q V (inject₁ t) a)
        (atSym (poolEnc len T V (fsuc t) (tR zero) z≤n w′))
  ∷ []

-- ────────────────────────────────────────────────────────────────────
-- §4 C6：初始（t = 0）与终止（t = T）
-- ────────────────────────────────────────────────────────────────────
-- 初始：初态 + `p = 0`（左带为空，与 `NPT-initCfg` 的 `mkTC [] q blk inp` 一致）；
-- 左邻空白；右带第 k 格取 `inp k`（`inp` 已把「超过输入长度处为空白」内置；
-- 其与 `tm-emb` 的一致性属 G4/G5 的桥接，不在本件）。
-- 终止：`t = T` 时状态是接受态（对任意 `p`；裁决 §3.1）。

initR-bound : ∀ (len : ℕ) (k : Fin (suc len)) → toℕ k ≤ len + 0 + 0
initR-bound len k = ≤-trans (fin-le k) (≤-trans (m≤m+n len zero) (m≤m+n (len + 0) zero))

initClauses : ∀ (len T Q V : ℕ) (q₀ : Fin Q) (inp : Fin (suc len) → Fin V)
              (blk : Fin V)
            → List (List (ALit (TabAtom len T Q V)))
initClauses len T Q V q₀ inp blk =
  ((σ₊ , atSt fzero q₀ fzero) ∷ [])
  ∷ ((σ₊ , atSym (poolEnc len T V fzero (tL zero) z≤n blk)) ∷ [])
  ∷ map (λ k → (σ₊ , atSym (poolEnc len T V fzero (tR (toℕ k))
                                            (initR-bound len k) (inp k))) ∷ [])
        (allFin (suc len))

-- `Bool` 条件筛选（stdlib 的 `filter` 要 `Decidable`，这里用定义透明的版本，
-- 核对层才能保持 `refl`）
clKeepIf : ∀ {A : Set} → Bool → List A → List A
clKeepIf true  xs = xs
clKeepIf false _  = []

finalClauses : ∀ (len T Q V : ℕ) (acc : Fin Q → Bool)
             → List (List (ALit (TabAtom len T Q V)))
finalClauses len T Q V acc =
  map (σ₊ ,_)
      (concat (map (λ q → clKeepIf (acc q)
                             (map (λ p → atSt (fromℕ T) q p) (allFin (suc T))))
                   (allFin Q)))
  ∷ []

-- ────────────────────────────────────────────────────────────────────
-- §5 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

Cl-check-allFin-2 : allFin 2 ≡ fzero ∷ fsuc fzero ∷ []
Cl-check-allFin-2 = refl

-- pSuc：0 ↦ 1；封顶于 T
Cl-check-pSuc-0 : pSuc 2 fzero ≡ fsuc fzero
Cl-check-pSuc-0 = refl

Cl-check-pSuc-top : pSuc 2 (fsuc (fsuc fzero)) ≡ fsuc (fsuc fzero)
Cl-check-pSuc-top = refl

-- C1：两个符号 ⟹ 2 条子句（长子句 + 1 对）
Cl-check-symOneHot-len : length (symOneHot 1 1 2 2 (fsuc fzero) tH tt) ≡ 2
Cl-check-symOneHot-len = refl

-- C1：长子句是两个正文字，原子是两个符号槽
Cl-check-symOneHot-head :
  listHead [] (symOneHot 1 1 2 2 (fsuc fzero) tH tt)
  ≡ ((σ₊ , atSym (poolEnc 1 1 2 (fsuc fzero) tH tt fzero))
     ∷ (σ₊ , atSym (poolEnc 1 1 2 (fsuc fzero) tH tt (fsuc fzero)))
     ∷ [])
Cl-check-symOneHot-head = refl

-- C2：Q = 2、T = 1 ⟹ 每刻 (T+1)·Q = 4 个状态槽
Cl-check-stCells-len : length (stCells 1 1 2 2 fzero) ≡ 4
Cl-check-stCells-len = refl

-- C2：4 槽 ⟹ oneHot = 1 条长子句 + C(4,2) = 6 条成对子句 = 7
Cl-check-stOneHot-len : length (stOneHot 1 1 2 2 fzero) ≡ 7
Cl-check-stOneHot-len = refl

-- C4：右移支 2 条子句
Cl-check-trans-R-len :
  length (transClauses 1 1 2 2 (λ _ _ → (fzero , fzero , R)) fzero fzero fzero fzero)
  ≡ 2
Cl-check-trans-R-len = refl

-- C4：左移两支都给 2 条子句，但目标不同（p=0 写新 tH；p=suc n 写新 tR 0）
Cl-check-trans-Lp0-len :
  length (transClauses 1 1 2 2 (λ _ _ → (fzero , fzero , L)) fzero fzero fzero fzero)
  ≡ 2
Cl-check-trans-Lp0-len = refl

Cl-check-trans-Lsuc-len :
  length (transClauses 1 1 2 2 (λ _ _ → (fzero , fzero , L)) fzero fzero fzero
                       (fsuc fzero))
  ≡ 2
Cl-check-trans-Lsuc-len = refl

-- C6：初始族 = 初态 1 + 左邻 1 + 右带 (len+1) = 2 + 2 = 4（len = 1）
Cl-check-init-len :
  length (initClauses 1 1 2 2 fzero (λ _ → fzero) fzero) ≡ 4
Cl-check-init-len = refl

-- C6：终止族 = 1 条长子句；全接受 ⟹ 文字数 = Q·(T+1) = 2·2 = 4
Cl-check-final-len :
  length (listHead [] (finalClauses 1 1 2 2 (λ _ → true))) ≡ 4
Cl-check-final-len = refl

-- 0 postulate / 0 hole。
