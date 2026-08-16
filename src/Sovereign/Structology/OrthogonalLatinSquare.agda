{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.OrthogonalLatinSquare
-- 正交拉丁方 → 幻方 (Euler 构造, 0 postulate)
--
-- 【术语边界】本模块「幻方」= 数学数字幻方（行列对角线和相等）。
-- 非卢先生「矢量方向/变量计数」幻方（阶数 = 同时在变的矢量方向个数）。
-- 辨析与知识库依据见 docs/cross-level/magic-square-terminology.md
--
-- 深度证明: M₄ 幻方不再手写给定, 而是从一对正交拉丁方 L₁, L₂ 叠加导出:
--   M₄[i,j] = 4·L₁[i,j] + L₂[i,j] + 1     (符号 0..3, 叠加值 1..16)
--
-- 拉丁性   ⟹ 每行/列含 {0,1,2,3} 各一次 ⟹ Σ = 6 ⟹ 行/列和 = 4·6 + 6 + 4 = 34
-- 正交性   ⟹ 16 个叠加值两两不同 ⟹ {1..16} 完整 (正规幻方)
-- 对角     ⟹ 具体 L₁, L₂ (断对角拉丁方) 额外使两条对角线和 = 34
--
-- 一般 Euler 定理 (任意奇数 n, 或 GF(q) 上的任意阶): 正交拉丁方对 (L₁,L₂)
-- 叠加 M = n·L₁ + L₂ + 1 自动给出半幻方 (行列和 = n(n²+1)/2); 正交性保证
-- 16 元互异。本模块在 n=4 逐 case 全证 (0 postulate, 全 refl)。
--
-- 与本体系连接: 此 M₄ 与 MagicSquareM4.agda 的 M₄ 逐元素一致 (euler-is-M4),
-- 后者经 M4CRTBridge.agda 投影到 CRT 模域 {34,0,16,-16}。故本模块把
-- "幻方矩阵" 从给定升级为构造推导, 再送入既有 CRT 桥。

module Sovereign.Structology.OrthogonalLatinSquare where

open import Data.Nat using (ℕ; _+_; _*_; _≟_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map; lookup; zipWith)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does)

--------------------------------------------------------------------------------
-- §1. 两个正交拉丁方 L₁, L₂ (4 阶, 符号 0..3)
--------------------------------------------------------------------------------

L1 : Vec (Vec ℕ 4) 4
L1 =
  (2 ∷ 1 ∷ 3 ∷ 0 ∷ []) ∷
  (0 ∷ 3 ∷ 1 ∷ 2 ∷ []) ∷
  (1 ∷ 2 ∷ 0 ∷ 3 ∷ []) ∷
  (3 ∷ 0 ∷ 2 ∷ 1 ∷ []) ∷
  []

L2 : Vec (Vec ℕ 4) 4
L2 =
  (2 ∷ 0 ∷ 1 ∷ 3 ∷ []) ∷
  (1 ∷ 3 ∷ 2 ∷ 0 ∷ []) ∷
  (3 ∷ 1 ∷ 0 ∷ 2 ∷ []) ∷
  (0 ∷ 2 ∷ 3 ∷ 1 ∷ []) ∷
  []

--------------------------------------------------------------------------------
-- §2. 拉丁性: 每行每列是 {0,1,2,3} 的排列
--------------------------------------------------------------------------------

-- 符号 x 在向量中出现的次数
count : ℕ → {n : ℕ} → Vec ℕ n → ℕ
count x [] = 0
count x (y ∷ ys) = (if does (x ≟ y) then 1 else 0) + count x ys

-- 4 元行是拉丁的 ⟺ {0,1,2,3} 各出现恰一次
isLatinRow : Vec ℕ 4 → Set
isLatinRow v =
  (count 0 v ≡ 1) × (count 1 v ≡ 1) × (count 2 v ≡ 1) × (count 3 v ≡ 1)

-- 列提取
column : Vec (Vec ℕ 4) 4 → Fin 4 → Vec ℕ 4
column M j = map (λ row → lookup row j) M

-- 4 阶拉丁方: 4 行 + 4 列均拉丁
isLatinSquare : Vec (Vec ℕ 4) 4 → Set
isLatinSquare M =
  isLatinRow (lookup M zero) × isLatinRow (lookup M (suc zero)) ×
  isLatinRow (lookup M (suc (suc zero))) × isLatinRow (lookup M (suc (suc (suc zero)))) ×
  isLatinRow (column M zero) × isLatinRow (column M (suc zero)) ×
  isLatinRow (column M (suc (suc zero))) × isLatinRow (column M (suc (suc (suc zero))))

L1-latin : isLatinSquare L1
L1-latin =
  (refl , refl , refl , refl) , (refl , refl , refl , refl) ,
  (refl , refl , refl , refl) , (refl , refl , refl , refl) ,
  (refl , refl , refl , refl) , (refl , refl , refl , refl) ,
  (refl , refl , refl , refl) , (refl , refl , refl , refl)

L2-latin : isLatinSquare L2
L2-latin =
  (refl , refl , refl , refl) , (refl , refl , refl , refl) ,
  (refl , refl , refl , refl) , (refl , refl , refl , refl) ,
  (refl , refl , refl , refl) , (refl , refl , refl , refl) ,
  (refl , refl , refl , refl) , (refl , refl , refl , refl)

--------------------------------------------------------------------------------
-- §3. 正交性: 叠加值 4·L₁+L₂ (0..15) 两两不同
--------------------------------------------------------------------------------

-- 16 个叠加值 (行主序, 0-based)
super0 : Vec ℕ 16
super0 =
  (4 * 2 + 2) ∷ (4 * 1 + 0) ∷ (4 * 3 + 1) ∷ (4 * 0 + 3) ∷
  (4 * 0 + 1) ∷ (4 * 3 + 3) ∷ (4 * 1 + 2) ∷ (4 * 2 + 0) ∷
  (4 * 1 + 3) ∷ (4 * 2 + 1) ∷ (4 * 0 + 0) ∷ (4 * 3 + 2) ∷
  (4 * 3 + 0) ∷ (4 * 0 + 2) ∷ (4 * 2 + 3) ∷ (4 * 1 + 1) ∷
  []

-- x 是否出现在 xs 中 (可判定)
elem? : ℕ → {n : ℕ} → Vec ℕ n → Bool
elem? x [] = false
elem? x (y ∷ ys) = does (x ≟ y) ∨ elem? x ys

-- 无重复元素
allDistinct : {n : ℕ} → Vec ℕ n → Bool
allDistinct [] = true
allDistinct (x ∷ xs) = not (elem? x xs) ∧ allDistinct xs

-- 正交性: 16 个叠加值两两不同 (⟺ 双射 Fin4×Fin4 → Fin16)
orthogonal : allDistinct super0 ≡ true
orthogonal = refl

--------------------------------------------------------------------------------
-- §4. Euler 叠加: M[i,j] = 4·L₁[i,j] + L₂[i,j] + 1  (1..16)
--------------------------------------------------------------------------------

superpose : Vec (Vec ℕ 4) 4
superpose = zipWith (zipWith (λ a b → 4 * a + b + 1)) L1 L2

-- 与既有 M₄ (MagicSquareM4.agda) 逐元素一致的矩阵
M4 : Vec (Vec ℕ 4) 4
M4 =
  (11 ∷ 5  ∷ 14 ∷ 4  ∷ []) ∷
  (2  ∷ 16 ∷ 7  ∷ 9  ∷ []) ∷
  (8  ∷ 10 ∷ 1  ∷ 15 ∷ []) ∷
  (13 ∷ 3  ∷ 12 ∷ 6  ∷ []) ∷
  []

-- 核心连接: Euler 叠加结果 = 既有 M₄ 幻方
euler-is-M4 : superpose ≡ M4
euler-is-M4 = refl

--------------------------------------------------------------------------------
-- §5. 幻方性质: 行/列/对角和 = 幻常数 34 = n(n²+1)/2
--------------------------------------------------------------------------------

sum4 : Vec ℕ 4 → ℕ
sum4 (a ∷ b ∷ c ∷ d ∷ []) = a + b + c + d

rowSum : Vec (Vec ℕ 4) 4 → Fin 4 → ℕ
rowSum M i = sum4 (lookup M i)

diagSum : Vec (Vec ℕ 4) 4 → ℕ
diagSum M =
  lookup (lookup M zero) zero
  + lookup (lookup M (suc zero)) (suc zero)
  + lookup (lookup M (suc (suc zero))) (suc (suc zero))
  + lookup (lookup M (suc (suc (suc zero)))) (suc (suc (suc zero)))

antidiagSum : Vec (Vec ℕ 4) 4 → ℕ
antidiagSum M =
  lookup (lookup M zero) (suc (suc (suc zero)))
  + lookup (lookup M (suc zero)) (suc (suc zero))
  + lookup (lookup M (suc (suc zero))) (suc zero)
  + lookup (lookup M (suc (suc (suc zero)))) zero

magicConstant : ℕ
magicConstant = 34

-- 行和 = 幻常数
euler-row-magic :
  rowSum superpose zero ≡ magicConstant ×
  rowSum superpose (suc zero) ≡ magicConstant ×
  rowSum superpose (suc (suc zero)) ≡ magicConstant ×
  rowSum superpose (suc (suc (suc zero))) ≡ magicConstant
euler-row-magic = refl , refl , refl , refl

-- 列和 = 幻常数
euler-col-magic :
  sum4 (column superpose zero) ≡ magicConstant ×
  sum4 (column superpose (suc zero)) ≡ magicConstant ×
  sum4 (column superpose (suc (suc zero))) ≡ magicConstant ×
  sum4 (column superpose (suc (suc (suc zero)))) ≡ magicConstant
euler-col-magic = refl , refl , refl , refl

-- 对角和 = 幻常数
euler-diag-magic : diagSum superpose ≡ magicConstant × antidiagSum superpose ≡ magicConstant
euler-diag-magic = refl , refl

-- 幻常数代数 (n=4): 每行含 {0..3} 各一次, Σ=6, 故 4·6 + 6 + 4 = 34
sum0to3 : 0 + 1 + 2 + 3 ≡ 6
sum0to3 = refl

euler-magic-formula : 4 * 6 + 6 + 4 ≡ 34
euler-magic-formula = refl

-- 0 postulate.
