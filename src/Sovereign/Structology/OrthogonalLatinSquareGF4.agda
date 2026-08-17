{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.OrthogonalLatinSquareGF4
-- GF(4) 域公式 → 正交拉丁方 → 半幻方 (0 postulate)
--
-- 域生成: L1(i,j) = i + j,  L2(i,j) = α·i + j  (GF(4) 加法/乘法)
-- 两者拉丁且正交 (16 对互异), Euler 叠加 M = 4·L1 + L2 + 1 是半幻方
-- (行和=列和=34)。
--
-- 【重要更正】本模块的 genL1/genL2 与 OrthogonalLatinSquare.agda 的手写 L1/L2
-- (来自 Dürer M₄ 分解) 不是同一对: 域仿射公式给出半幻方 (对角 ≠ 34), 而 M₄ 分解
-- 给出完全幻方 (对角也 = 34)。故 genL1 ≢ L1, 之前「genL1-eq-L1 = refl」的假设错误。
-- 本模块证明 GF(4) 域论链「域 → 正交拉丁方 → 半幻方」, 与 M₄ 的完全幻方互补。

module Sovereign.Structology.OrthogonalLatinSquareGF4 where

open import Data.Nat using (ℕ; _+_; _*_; _≟_)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Vec using (Vec; []; _∷_; map; lookup; zipWith; allFin; _++_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does)

open import Sovereign.Structology.GF4
  using (GF4; g0; g1; ga; gb; add4; mul4; toFin; fromFin)

--------------------------------------------------------------------------------
-- §1. GF(4) 域生成的两个拉丁方 (ℕ 索引)
--------------------------------------------------------------------------------

genL1 : Vec (Vec ℕ 4) 4
genL1 = map (λ i → map (λ j → toℕ (toFin (add4 (fromFin i) (fromFin j)))) (allFin 4)) (allFin 4)

genL2 : Vec (Vec ℕ 4) 4
genL2 = map (λ i → map (λ j → toℕ (toFin (add4 (mul4 ga (fromFin i)) (fromFin j)))) (allFin 4)) (allFin 4)

--------------------------------------------------------------------------------
-- §2. 拉丁性
--------------------------------------------------------------------------------

count : ℕ → {n : ℕ} → Vec ℕ n → ℕ
count x [] = 0
count x (y ∷ ys) = (if does (x ≟ y) then 1 else 0) + count x ys

isLatinRow : Vec ℕ 4 → Set
isLatinRow v = (count 0 v ≡ 1) × (count 1 v ≡ 1) × (count 2 v ≡ 1) × (count 3 v ≡ 1)

column : Vec (Vec ℕ 4) 4 → Fin 4 → Vec ℕ 4
column M j = map (λ row → lookup row j) M

isLatinSquare : Vec (Vec ℕ 4) 4 → Set
isLatinSquare M = isLatinRow (lookup M zero) × isLatinRow (lookup M (suc zero)) × isLatinRow (lookup M (suc (suc zero))) × isLatinRow (lookup M (suc (suc (suc zero)))) × isLatinRow (column M zero) × isLatinRow (column M (suc zero)) × isLatinRow (column M (suc (suc zero))) × isLatinRow (column M (suc (suc (suc zero))))

genL1-latin : isLatinSquare genL1
genL1-latin =
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl)
genL2-latin : isLatinSquare genL2
genL2-latin =
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl),
  (refl , refl , refl , refl)

--------------------------------------------------------------------------------
-- §3. 正交性 (16 对互异)
--------------------------------------------------------------------------------

flatten4 : {n : ℕ} → Vec (Vec ℕ 4) n → Vec ℕ (n * 4)
flatten4 [] = []
flatten4 (row ∷ rows) = row ++ flatten4 rows

super0 : Vec ℕ 16
super0 = flatten4 (zipWith (zipWith (λ a b → 4 * a + b)) genL1 genL2)

elem? : ℕ → {n : ℕ} → Vec ℕ n → Bool
elem? x [] = false
elem? x (y ∷ ys) = does (x ≟ y) ∨ elem? x ys

allDistinct : {n : ℕ} → Vec ℕ n → Bool
allDistinct [] = true
allDistinct (x ∷ xs) = not (elem? x xs) ∧ allDistinct xs

orthogonal : allDistinct super0 ≡ true
orthogonal = refl

--------------------------------------------------------------------------------
-- §4. Euler 叠加 → 半幻方 (行和=列和=34)
--------------------------------------------------------------------------------

superpose : Vec (Vec ℕ 4) 4
superpose = zipWith (zipWith (λ a b → 4 * a + b + 1)) genL1 genL2

sum4 : Vec ℕ 4 → ℕ
sum4 (a ∷ b ∷ c ∷ d ∷ []) = a + b + c + d

rowSum : Vec (Vec ℕ 4) 4 → Fin 4 → ℕ
rowSum M i = sum4 (lookup M i)

colSum : Vec (Vec ℕ 4) 4 → Fin 4 → ℕ
colSum M j = sum4 (column M j)

semi-magic-rows : rowSum superpose zero ≡ 34 × rowSum superpose (suc zero) ≡ 34 × rowSum superpose (suc (suc zero)) ≡ 34 × rowSum superpose (suc (suc (suc zero))) ≡ 34
semi-magic-rows = refl , refl , refl , refl

semi-magic-cols : colSum superpose zero ≡ 34 × colSum superpose (suc zero) ≡ 34 × colSum superpose (suc (suc zero)) ≡ 34 × colSum superpose (suc (suc (suc zero))) ≡ 34
semi-magic-cols = refl , refl , refl , refl

-- 幻常数代数: 每行含 {0,1,2,3} 各一次, Σ=6, 故 4·6 + 6 + 4 = 34
sum0to3 : 0 + 1 + 2 + 3 ≡ 6
sum0to3 = refl
euler-formula : 4 * 6 + 6 + 4 ≡ 34
euler-formula = refl

-- 0 postulate.
