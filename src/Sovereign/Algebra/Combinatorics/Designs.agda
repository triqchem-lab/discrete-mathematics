{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.Combinatorics.Designs
-- 组合设计基础：区组设计（参数形定义层）与 Latin 方（含公理化面）
--
-- 数学背景：2-(v,k,λ) 区组设计 = v 点集 + k 元区组族 + 点对覆盖数 λ
--   （Fano 平面 2-(7,3,1) 经典例）；Latin 方 = n×n 表且各行各列单射（=双射，方阵面）。
--   本模块落**定义层 + 三角设计 2-(3,2,1) 最小非平凡实例 + 2 阶循环 Latin 方**——
--   构造性深件（Fano 构造/正交 Latin 方/Steiner 三元系分类）立界注记不硬拱。
-- 核心原则：
-- 1. 关系入定义（BlockDesign 参数面 record 承载；IsLatin 公理独立 record——导出性质不入字段）
-- 2. 参数核对走 ℕ 计算面（refl 级——≤27 case 边界内）
-- 3. 立界注记显式（不设空壳签名——零洞纪律）
-- 4. Fin 构造子 renaming（fzero/fsuc 库约定）；量测纪律（真退出码）
--
-- 包含：eqFin · inL · countB · BlockDesign · tri-design · 参数核对 ×6 ·
--       LatinSquare · IsLatin · lat2（2 阶循环方）· 行列单射实例 · 立界注记

module Sovereign.Algebra.Combinatorics.Designs where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- §1 基础件（Fin 相等/包含/计数——具名全层）
------------------------------------------------------------------------

-- Fin 逐位相等（递归形——免 _≟_ 依赖）
eqFin : ∀ {n} → Fin n → Fin n → Bool
eqFin fzero fzero = true
eqFin fzero (fsuc _) = false
eqFin (fsuc _) fzero = false
eqFin (fsuc m) (fsuc k) = eqFin m k

-- 点属列表（Bool 形）
inL : ∀ {n} → Fin n → List (Fin n) → Bool
inL x [] = false
inL x (y ∷ ys) = eqFin x y || inL x ys
  where
  _||_ : Bool → Bool → Bool
  true || _ = true
  false || b = b

-- 点对共现计数：含 x 且含 y 的区组数
andB : Bool → Bool → Bool
andB true b = b
andB false _ = false

addIf : Bool → ℕ → ℕ
addIf true m = suc m
addIf false m = m

countB : ∀ {n} → Fin n → Fin n → List (List (Fin n)) → ℕ
countB x y [] = zero
countB x y (B ∷ Bs) = addIf (andB (inL x B) (inL y B)) (countB x y Bs)

------------------------------------------------------------------------
-- §2 区组设计（参数形定义层——record 承载）
------------------------------------------------------------------------

-- 2-(v,k,λ) 设计数据面：参数三元 + 区组族 + 点集型
--   公理面（区组大小=k / 点对覆盖=λ）由 IsDesign 形独立承载（§2.1 立界）——
--   数据/公理分离：record 只携数据，公理不入字段（presentation 最小性）
record BlockDesign (P : Set) : Set₁ where
  field
    v k lam : ℕ
    blocks : List (List P)

------------------------------------------------------------------------
-- §3 三角设计 2-(3,2,1)——最小非平凡实例（三顶点三边）
------------------------------------------------------------------------

Tri : Set
Tri = Fin 3

b01 b12 b02 : List Tri
b01 = fzero ∷ fsuc fzero ∷ []
b12 = fsuc fzero ∷ fsuc (fsuc fzero) ∷ []
b02 = fzero ∷ fsuc (fsuc fzero) ∷ []

tri-blocks : List (List Tri)
tri-blocks = b01 ∷ b12 ∷ b02 ∷ []

tri-design : BlockDesign Tri
tri-design = record { v = 3; k = 2; lam = 1; blocks = tri-blocks }

-- 参数核对层（全 refl 级——ℕ 计算面）
check-size-b01 : length b01 ≡ 2
check-size-b01 = refl

check-size-b12 : length b12 ≡ 2
check-size-b12 = refl

check-size-b02 : length b02 ≡ 2
check-size-b02 = refl

-- 点对覆盖核对：三对各恰 1 区组（λ=1）
check-pair-01 : countB fzero (fsuc fzero) tri-blocks ≡ 1
check-pair-01 = refl

check-pair-12 : countB (fsuc fzero) (fsuc (fsuc fzero)) tri-blocks ≡ 1
check-pair-12 = refl

check-pair-02 : countB fzero (fsuc (fsuc fzero)) tri-blocks ≡ 1
check-pair-02 = refl

------------------------------------------------------------------------
-- §4 Latin 方（定义层 + 公理面 + 2 阶循环方实例）
------------------------------------------------------------------------

-- 表载体（数据面）
record LatinSquare (n : ℕ) : Set where
  field
    tab : Fin n → Fin n → Fin n

-- 公理面（关系入定义：行列单射 = Latin 性）
record IsLatin {n : ℕ} (L : LatinSquare n) : Set where
  open LatinSquare L
  field
    row-inj : ∀ i (j j′ : Fin n) → tab i j ≡ tab i j′ → j ≡ j′
    col-inj : ∀ j (i i′ : Fin n) → tab i j ≡ tab i′ j → i ≡ i′

-- 2 阶循环方：tab i j = i ⊞ j（mod 2 逐位形——4 宫全构造子）
tab2 : Fin 2 → Fin 2 → Fin 2
tab2 fzero fzero = fzero
tab2 fzero (fsuc fzero) = fsuc fzero
tab2 (fsuc fzero) fzero = fsuc fzero
tab2 (fsuc fzero) (fsuc fzero) = fzero

lat2 : LatinSquare 2
lat2 = record { tab = tab2 }

-- 行列单射实例（2 阶全 case——结构异即矛盾消解）
lat2-row-inj : ∀ i (j j′ : Fin 2) → tab2 i j ≡ tab2 i j′ → j ≡ j′
lat2-row-inj fzero fzero fzero _ = refl
lat2-row-inj fzero fzero (fsuc fzero) ()
lat2-row-inj fzero (fsuc fzero) fzero ()
lat2-row-inj fzero (fsuc fzero) (fsuc fzero) _ = refl
lat2-row-inj (fsuc fzero) fzero fzero _ = refl
lat2-row-inj (fsuc fzero) fzero (fsuc fzero) ()
lat2-row-inj (fsuc fzero) (fsuc fzero) fzero ()
lat2-row-inj (fsuc fzero) (fsuc fzero) (fsuc fzero) _ = refl

lat2-col-inj : ∀ j (i i′ : Fin 2) → tab2 i j ≡ tab2 i′ j → i ≡ i′
lat2-col-inj fzero fzero fzero _ = refl
lat2-col-inj fzero fzero (fsuc fzero) ()
lat2-col-inj fzero (fsuc fzero) fzero ()
lat2-col-inj fzero (fsuc fzero) (fsuc fzero) _ = refl
lat2-col-inj (fsuc fzero) fzero fzero _ = refl
lat2-col-inj (fsuc fzero) fzero (fsuc fzero) ()
lat2-col-inj (fsuc fzero) (fsuc fzero) fzero ()
lat2-col-inj (fsuc fzero) (fsuc fzero) (fsuc fzero) _ = refl

lat2-latin : IsLatin lat2
lat2-latin = record { row-inj = lat2-row-inj; col-inj = lat2-col-inj }

-- 核对层（表值三件——defeq 级）
check-tab2-01 : tab2 fzero (fsuc fzero) ≡ fsuc fzero
check-tab2-01 = refl

check-tab2-11 : tab2 (fsuc fzero) (fsuc fzero) ≡ fzero
check-tab2-11 = refl

------------------------------------------------------------------------
-- §5 立界注记（不设空壳签名——深件诚实边界）
-- (i)   IsDesign 公理面（区组大小/点对覆盖的字段化）+ tri-design 全字段实例
--       （点对计数引理族 ~30-50 行）
-- (ii)  Fano 平面 2-(7,3,1) 构造（~100-150 行——PG²(2) 七点七线）
-- (iii) 正交 Latin 方存在性（Euler 36 军官问题面——深件）
-- (iv)  Steiner 三元系分类（S(v,3) 计数——深件 300+）
------------------------------------------------------------------------
