{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Complexity.Tableau-Clauses
-- tableau 的子句族（原子层，**不含语义**）—— 里程碑 M3c 闸门 G3
--
-- 【本件做什么】把 tableau 的六族子句写成**具体的 `List (List (ALit A))`**：
-- 每格「恰好一个符号」、每刻「恰好一个（状态, 头位）」、一步转移、非头不变、
-- 初始格局、终止格局，最后拼成 `tableauOf`。本件**只给形状**：满足性 ⟹ 运行
-- 的论证（G4/G5）在 `Tableau-Sem.agda`，本件不声称任何语义定理。
--
-- 【原子类型为什么暂时只有符号格】子句族的原子要分两类：符号格 `(t, o, a)` 与
-- 状态格 `(t, q, …)`。符号格已经定死（G2 的池：`Fin (poolSize len T V)`）；
-- 状态格的**形状取决于 C4 的左边界分叉**（见
-- `docs/decisions/M3c-C4-左边界分叉-2026-10-30.md`）：
--   · 若状态原子带上头的绝对位置 `(t, q, p)`，则「左带是否为空」变成局部可判；
--   · 若不带上，则 `tShiftL` 与 `tShiftLN` 之间无法在窗口内选支。
-- 所以 §1 先只立符号族（与分叉无关），状态族与转移族等裁决落地后追加。
--
-- 分级约定：〔结构定义〕/〔结构证明〕/〔refl 枚举〕/〔立界注记〕（同 TimeBound）。
-- 0 postulate / 0 hole。

module Sovereign.Algebra.Complexity.Tableau-Clauses where

open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; s≤s⁻¹)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Sovereign.Algebra.Complexity.SATMember using (Sign; σ₊; σ₋)
open import Sovereign.Algebra.Complexity.Tableau
  using (ALit; TEnv; oneHot; satAFormula)
open import Sovereign.Algebra.Complexity.Tableau-Tape using (TOff; tH; tL; tR; InOff)
open import Sovereign.Algebra.Complexity.Tableau-Pool using (poolSize; poolEnc)

-- ────────────────────────────────────────────────────────────────────
-- §0 枚举件（六族共用）〔结构定义〕
-- ────────────────────────────────────────────────────────────────────

-- `Fin n` 的全枚举（stdlib 没有 `allFin` 这种 List 形态；`tabulate` 是 Vec）
allFin : (n : ℕ) → List (Fin n)
allFin zero    = []
allFin (suc n) = fzero ∷ map fsuc (allFin n)

-- 取表头（带默认值；核对层要用它看首条子句的形状）
listHead : ∀ {A : Set} → A → List A → A
listHead d []      = d
listHead _ (x ∷ _) = x

-- `Fin (suc n)` 的取值界：`toℕ k ≤ n`（三族都要它来喂 `poolEnc`/`InOff`）
fin-le : ∀ {n : ℕ} (k : Fin (suc n)) → toℕ k ≤ n
fin-le k = s≤s⁻¹ (toℕ<n k)

-- 带界内性见证的偏移：`TOff` 不是 `Fin`，无法无见证枚举；把见证放进 Σ 里，
-- 下游（C1/C3/C4/C5）取用时不必再构造证明。
OffW : (len t : ℕ) → Set
OffW len t = Σ TOff (InOff len t)

-- 时刻 t 的窗口全枚举：头格 + 左 k ≤ t + 右 k ≤ len + t + t
allOffW : (len t : ℕ) → List (OffW len t)
allOffW len t =
  (tH , tt)
  ∷ map (λ k → tL (toℕ k) , fin-le k) (allFin (suc t))
  ++ map (λ k → tR (toℕ k) , fin-le k) (allFin (suc (len + t + t)))

-- ────────────────────────────────────────────────────────────────────
-- §1 C1：每格「恰好一个符号」〔结构定义〕
-- ────────────────────────────────────────────────────────────────────
-- 与 M3a 的 `oneHot` 直接对接：符号族就是「池号」的列表，`oneHot` 负责
-- 「至少一个」（长子句）+「至多一个」（成对 `¬u ∨ ¬v`）。三值语义下后者强制
-- 未选中者取 T₂（见 Tableau.agda 头注），这是「一字一格」的准确编码。

symCells : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff) (h : InOff len (toℕ t) o)
         → List (Fin (poolSize len T V))
symCells len T V t o h = map (λ a → poolEnc len T V t o h a) (allFin V)

symOneHot : ∀ (len T V : ℕ) (t : Fin (suc T)) (o : TOff) (h : InOff len (toℕ t) o)
          → List (List (ALit (Fin (poolSize len T V))))
symOneHot len T V t o h = oneHot (symCells len T V t o h)

-- ────────────────────────────────────────────────────────────────────
-- §2 核对层〔refl 枚举〕
-- ────────────────────────────────────────────────────────────────────

Cl-check-allFin-2 : allFin 2 ≡ fzero ∷ fsuc fzero ∷ []
Cl-check-allFin-2 = refl

-- len = 1、T = 1、V = 2、t = 1、o = tH：两个符号槽都来自池编码
Cl-check-symCells :
  symCells 1 1 2 (fsuc fzero) tH tt
  ≡ (poolEnc 1 1 2 (fsuc fzero) tH tt fzero
     ∷ poolEnc 1 1 2 (fsuc fzero) tH tt (fsuc fzero)
     ∷ [])
Cl-check-symCells = refl

-- 两个符号 ⟹ `oneHot` 给 2 条子句（长子句 + 1 条成对子句）
Cl-check-symOneHot-len : length (symOneHot 1 1 2 (fsuc fzero) tH tt) ≡ 2
Cl-check-symOneHot-len = refl

-- 长子句的形状：首条子句是 2 个**正**文字，且原子正好是两个符号槽
Cl-check-symOneHot-head :
  listHead [] (symOneHot 1 1 2 (fsuc fzero) tH tt)
  ≡ ((σ₊ , poolEnc 1 1 2 (fsuc fzero) tH tt fzero)
     ∷ (σ₊ , poolEnc 1 1 2 (fsuc fzero) tH tt (fsuc fzero))
     ∷ [])
Cl-check-symOneHot-head = refl

-- 0 postulate / 0 hole。
