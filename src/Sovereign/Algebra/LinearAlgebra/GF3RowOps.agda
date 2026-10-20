{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LinearAlgebra.GF3RowOps
-- GF(3) 上的行运算核心 —— 为「秩-零化度定理」铺路（T4 / A1a，2026-10-20）
--
-- 数学背景
--   要在 Agda 里说「`laplacian6` 的 rank = 454」，必须先有 GF(3) 上的初等线性代数。
--   本模块只做**最底层**：行向量、矩阵、初等行变换（加行 / 取负），以及它们的
--   **可逆性**——这是「行变换保持行空间」的代数根据，也是秩不变性的第一块砖。
--
-- 核心原则
--   ① 行 = `Vec Trit n`（GF(3) 幅度），矩阵 = 行的 `Vec`
--   ② 初等行变换必须在**保持行空间**的意义下可逆：`(r +R a) +R negR a ≡ r`
--   ③ 逐点引理用 3/9 情形穷举；向量层用 `zipWith`/`map` 同余搬运
--   ④ 不引入任何浮点、不假设排中律
--
-- 包含：Row / Matrix / _+R_ / negR / p-elim / p-comm / zipWith-cong / add-then-cancel / negR²

-- ⚠ **与 cubical 矩阵库的关系（2026-10-20 补记，必读）**
-- ============================================================================
-- 本地 `/data/work/functional-programming/cubical/` **已有**参数化的矩阵初等变换：
--   · `Cubical.Algebra.Matrix`（353 行）—— `FinMatrix` / `VecMatrix` / `flatten`
--   · `Cubical.Algebra.Matrix.RowTransformation`（**744 行**）—— `takeRows` / `combRows`
--     / `shufRows` / `takeTrans`（2 行一组的初等行变换）
--   · `Cubical.Algebra.Matrix.Elementaries`（321 行）—— `ElemTransformation (𝓡 : CommRing ℓ)`
--   · `Cubical.Algebra.IntegerMatrix.Smith` —— **Smith 标准形**（整数矩阵）
-- 它们是 `CommRing` 参数的模块函子 ⇒ **GF(3) 直接实例化** ✓。
--
-- **本模块的定位（不是重复的正当理由，只是差异说明）**：
--   ① 本库主流用 `≡`（命题相等），cubical 用 `Path`（`--cubical` 风格）；
--   ② 本模块是 GF(3) 专用（`Trit`），cubical 版是任意 `CommRing`；
--   ③ 本模块只 138 行、无 cubical 依赖，编译 4s。
-- **⇒ 若要 c ubical 那套通用件，优先用 cubical ✓；本模块只为「本库 `≡` 风格下的
--   GF(3) 最小自足件」而存在 ✗ —— 写新引理前**先看 cubical** ✗。**
--
module Sovereign.Algebra.LinearAlgebra.GF3RowOps where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.Properties using (&&-idʳ)
open import Data.Vec using (Vec; []; _∷_; map; zipWith; foldr; replicate)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)

--------------------------------------------------------------------------------
-- §1. 载体
--------------------------------------------------------------------------------

Row : ℕ → Set
Row n = Vec Trit n

Matrix : ℕ → ℕ → Set
Matrix m n = Vec (Row n) m

--------------------------------------------------------------------------------
-- §2. 初等行变换
--------------------------------------------------------------------------------

-- 行加法（逐分量 ⊕）
_+R_ : ∀ {n} → Row n → Row n → Row n
_+R_ = zipWith _⊕_

-- 行取负（逐分量 negate）
negR : ∀ {n} → Row n → Row n
negR = map negate

--------------------------------------------------------------------------------
-- §3. 逐点引理（GF(3) 上 3×3 情形穷举）
--------------------------------------------------------------------------------

-- `(a ⊕ b) ⊕ negate b ≡ a`：加行后取负可抵消
p-elim : ∀ a b → (a ⊕ b) ⊕ negate b ≡ a
p-elim T₀ T₀ = refl
p-elim T₀ T₁ = refl
p-elim T₀ T₂ = refl
p-elim T₁ T₀ = refl
p-elim T₁ T₁ = refl
p-elim T₁ T₂ = refl
p-elim T₂ T₀ = refl
p-elim T₂ T₁ = refl
p-elim T₂ T₂ = refl

-- 双重取负复原
p-neg² : ∀ a → negate (negate a) ≡ a
p-neg² T₀ = refl
p-neg² T₁ = refl
p-neg² T₂ = refl

--------------------------------------------------------------------------------
-- §4. 向量层搬运（同余）
--------------------------------------------------------------------------------

-- `zipWith` 在点态相等的函数下同余
zipWith-cong :
  ∀ {n} {f g : Trit → Trit → Trit} →
    (∀ a b → f a b ≡ g a b) → (u v : Vec Trit n) → zipWith f u v ≡ zipWith g u v
zipWith-cong h []       []       = refl
zipWith-cong h (x ∷ xs) (y ∷ ys) = cong₂ _∷_ (h x y) (zipWith-cong h xs ys)

-- `map` 在点态相等的函数下同余
map-cong : ∀ {n} {f g : Trit → Trit} → (∀ a → f a ≡ g a) → (u : Vec Trit n) → map f u ≡ map g u
map-cong h []       = refl
map-cong h (x ∷ xs) = cong₂ _∷_ (h x) (map-cong h xs)

--------------------------------------------------------------------------------
-- §5. 主定理：初等行变换可逆（⇒ 保持行空间）
--------------------------------------------------------------------------------

-- ★ 加行后取负可完全抵消 —— 秩不变性的代数根据
add-then-cancel : ∀ {n} (r a : Row n) → (r +R a) +R negR a ≡ r
add-then-cancel []       []       = refl
add-then-cancel (x ∷ xs) (y ∷ ys) =
  cong₂ _∷_ (p-elim x y) (add-then-cancel xs ys)

-- 取负两次复原
negR² : ∀ {n} (u : Row n) → negR (negR u) ≡ u
negR² []       = refl
negR² (x ∷ xs) = cong₂ _∷_ (p-neg² x) (negR² xs)

--------------------------------------------------------------------------------
-- §6. 行缩放（标量乘）与可逆性
--------------------------------------------------------------------------------

-- 非零标量的逆（T₀ 处无意义，用 T₀ 占位 —— 调用方必须给非零前提）
inv3 : Trit → Trit
inv3 T₀ = T₀
inv3 T₁ = T₁
inv3 T₂ = T₂

-- 行缩放
scaleR : ∀ {n} → Trit → Row n → Row n
scaleR a = map (a ⊗_)

-- 逐点：非零标量缩放的抵消（`inv a ⊗ (a ⊗ x) ≡ x`）
p-scale-cancel : ∀ a x → a ≢ T₀ → inv3 a ⊗ (a ⊗ x) ≡ x
p-scale-cancel T₀ x a≠0 = ⊥-elim (a≠0 refl)
p-scale-cancel T₁ T₀ _ = refl
p-scale-cancel T₁ T₁ _ = refl
p-scale-cancel T₁ T₂ _ = refl
p-scale-cancel T₂ T₀ _ = refl
p-scale-cancel T₂ T₁ _ = refl
p-scale-cancel T₂ T₂ _ = refl

-- ★ 行缩放可逆（非零标量）⇒ 秩不变性的第二条根据
scale-cancel : ∀ {n} (a : Trit) (u : Row n) → a ≢ T₀ → scaleR (inv3 a) (scaleR a u) ≡ u
scale-cancel a []       a≠0 = refl
scale-cancel a (x ∷ xs) a≠0 =
  cong₂ _∷_ (p-scale-cancel a x a≠0) (scale-cancel a xs a≠0)

--------------------------------------------------------------------------------
-- §7. 零判定与非零行计数（`rank` 的定义基础）
--
-- `rank` 的构造性定义：先化到 echelon（行阶梯）形，再数**非零行**的个数。
-- 本节给出后半件（数非零行）；echelon 消元在 A1d。
--------------------------------------------------------------------------------

-- 标量零判定
isZeroT : Trit → Bool
isZeroT T₀ = true
isZeroT T₁ = false
isZeroT T₂ = false

-- 行是否全为零
isZeroRow : ∀ {n} → Row n → Bool
isZeroRow []       = true
isZeroRow (x ∷ xs) = if isZeroT x then isZeroRow xs else false

-- 非零行计数
countNonzero : ∀ {m n} → Matrix m n → ℕ
countNonzero {zero}  []       = zero
countNonzero {suc m} (r ∷ rs) =
  (if isZeroRow r then zero else suc zero) + countNonzero rs

-- 全零行判零
isZeroRow-replicate : ∀ n → isZeroRow (replicate n T₀) ≡ true
isZeroRow-replicate zero    = refl
isZeroRow-replicate (suc n) = isZeroRow-replicate n
