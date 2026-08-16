{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Structology.GF9MagicSquare
-- GF(9) = GF(3)[α]/(α²+1) 正交拉丁方 → 9 阶幻方 (Euler 构造, 0 postulate)
--
-- 深度证明: 三进制域 GF(3²) 上的正交拉丁方 L_λ[i,j] = idx(λ·el(i) + el(j))
-- 由域运算生成, 取 λ=α 与 λ=2α (Galois 共轭对 σ(α)=-α=2α, 即 C₂ 手征共轭),
-- Euler 叠加 M = 9·L₁ + L₂ + 1 得到 9 阶完全幻方 (幻常数 369)。
-- 拉丁性 ⟹ 行/列和 = 幻常数; 正交性 ⟹ 81 元互异 = {1..81} (正规幻方)。
-- 对应 Rust sov-validation/ternary_magic.rs 的数值核验。

module Sovereign.Structology.GF9MagicSquare where

open import Data.Nat using (ℕ; _+_; _*_; _≟_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map; lookup; zipWith; allFin; _++_)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does)

open import Sovereign.Base.Trit using (Trit; T₀; T₁; T₂; _⊕_; _⊗_; negate)
open import Sovereign.Algebra.GF9 using (GF9; _+gf9_; _*gf9_)

--------------------------------------------------------------------------------
-- §1. GF(9) 的 9 个元素枚举: idx = a*3 + b, el(i) = a + bα
--------------------------------------------------------------------------------

el : Fin 9 → GF9
el zero = T₀ , T₀
el (suc zero) = T₀ , T₁
el (suc (suc zero)) = T₀ , T₂
el (suc (suc (suc zero))) = T₁ , T₀
el (suc (suc (suc (suc zero)))) = T₁ , T₁
el (suc (suc (suc (suc (suc zero))))) = T₁ , T₂
el (suc (suc (suc (suc (suc (suc zero)))))) = T₂ , T₀
el (suc (suc (suc (suc (suc (suc (suc zero))))))) = T₂ , T₁
el (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = T₂ , T₂

idx : GF9 → ℕ
idx (T₀ , T₀) = 0
idx (T₀ , T₁) = 1
idx (T₀ , T₂) = 2
idx (T₁ , T₀) = 3
idx (T₁ , T₁) = 4
idx (T₁ , T₂) = 5
idx (T₂ , T₀) = 6
idx (T₂ , T₁) = 7
idx (T₂ , T₂) = 8

--------------------------------------------------------------------------------
-- §2. 拉丁方 L_λ[i,j] = idx(λ·el(i) + el(j))
--------------------------------------------------------------------------------

L : GF9 → Vec (Vec ℕ 9) 9
L lam = map (λ i → map (λ j → idx ((lam *gf9 el i) +gf9 (el j))) (allFin 9)) (allFin 9)

lam1 : GF9
lam1 = T₀ , T₁   -- α
lam2 : GF9
lam2 = T₀ , T₂   -- 2α = σ(α) (Frobenius 共轭)

L1 : Vec (Vec ℕ 9) 9
L1 = L lam1
L2 : Vec (Vec ℕ 9) 9
L2 = L lam2

--------------------------------------------------------------------------------
-- §3. 拉丁性: 每行每列是 {0..8} 的排列
--------------------------------------------------------------------------------

count : ℕ → {n : ℕ} → Vec ℕ n → ℕ
count x [] = 0
count x (y ∷ ys) = (if does (x ≟ y) then 1 else 0) + count x ys

isLatinRow9 : Vec ℕ 9 → Set
isLatinRow9 v = (count 0 v ≡ 1) × (count 1 v ≡ 1) × (count 2 v ≡ 1) × (count 3 v ≡ 1) × (count 4 v ≡ 1) × (count 5 v ≡ 1) × (count 6 v ≡ 1) × (count 7 v ≡ 1) × (count 8 v ≡ 1)

column : Vec (Vec ℕ 9) 9 → Fin 9 → Vec ℕ 9
column M j = map (λ row → lookup row j) M

isLatinSquare9 : Vec (Vec ℕ 9) 9 → Set
isLatinSquare9 M = isLatinRow9 (lookup M zero) × isLatinRow9 (lookup M (suc zero)) × isLatinRow9 (lookup M (suc (suc zero))) × isLatinRow9 (lookup M (suc (suc (suc zero)))) × isLatinRow9 (lookup M (suc (suc (suc (suc zero))))) × isLatinRow9 (lookup M (suc (suc (suc (suc (suc zero)))))) × isLatinRow9 (lookup M (suc (suc (suc (suc (suc (suc zero))))))) × isLatinRow9 (lookup M (suc (suc (suc (suc (suc (suc (suc zero)))))))) × isLatinRow9 (lookup M (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) × isLatinRow9 (column M zero) × isLatinRow9 (column M (suc zero)) × isLatinRow9 (column M (suc (suc zero))) × isLatinRow9 (column M (suc (suc (suc zero)))) × isLatinRow9 (column M (suc (suc (suc (suc zero))))) × isLatinRow9 (column M (suc (suc (suc (suc (suc zero)))))) × isLatinRow9 (column M (suc (suc (suc (suc (suc (suc zero))))))) × isLatinRow9 (column M (suc (suc (suc (suc (suc (suc (suc zero)))))))) × isLatinRow9 (column M (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))

L1-latin : isLatinSquare9 L1
L1-latin =
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl)
L2-latin : isLatinSquare9 L2
L2-latin =
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl),
  (refl , refl , refl , refl , refl , refl , refl , refl , refl)

--------------------------------------------------------------------------------
-- §4. 正交性: 81 个叠加值 9·L₁+L₂ (0..80) 两两不同
--------------------------------------------------------------------------------

flatten9 : {n : ℕ} → Vec (Vec ℕ 9) n → Vec ℕ (n * 9)
flatten9 [] = []
flatten9 (row ∷ rows) = row ++ flatten9 rows

super0 : Vec ℕ 81
super0 = flatten9 (zipWith (zipWith (λ a b → 9 * a + b)) L1 L2)

elem? : ℕ → {n : ℕ} → Vec ℕ n → Bool
elem? x [] = false
elem? x (y ∷ ys) = does (x ≟ y) ∨ elem? x ys

allDistinct : {n : ℕ} → Vec ℕ n → Bool
allDistinct [] = true
allDistinct (x ∷ xs) = not (elem? x xs) ∧ allDistinct xs

orthogonal : allDistinct super0 ≡ true
orthogonal = refl

--------------------------------------------------------------------------------
-- §5. Euler 叠加 M = 9·L₁ + L₂ + 1 → 9 阶完全幻方 (幻常数 369)
--------------------------------------------------------------------------------

superpose : Vec (Vec ℕ 9) 9
superpose = zipWith (zipWith (λ a b → 9 * a + b + 1)) L1 L2

sum9 : Vec ℕ 9 → ℕ
sum9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ h ∷ i ∷ []) = a + b + c + d + e + f + g + h + i

rowSum : Vec (Vec ℕ 9) 9 → Fin 9 → ℕ
rowSum M i = sum9 (lookup M i)

colSum : Vec (Vec ℕ 9) 9 → Fin 9 → ℕ
colSum M j = sum9 (column M j)

diagSum : Vec (Vec ℕ 9) 9 → ℕ
diagSum M = sum9 (lookup (lookup M zero) zero ∷ lookup (lookup M (suc zero)) (suc zero) ∷ lookup (lookup M (suc (suc zero))) (suc (suc zero)) ∷ lookup (lookup M (suc (suc (suc zero)))) (suc (suc (suc zero))) ∷ lookup (lookup M (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) ∷ lookup (lookup M (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc (suc (suc zero))))) ∷ lookup (lookup M (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc (suc (suc (suc (suc zero)))))) ∷ lookup (lookup M (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∷ lookup (lookup M (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ∷ [])

antidiagSum : Vec (Vec ℕ 9) 9 → ℕ
antidiagSum M = sum9 (lookup (lookup M zero) (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ∷ lookup (lookup M (suc zero)) (suc (suc (suc (suc (suc (suc (suc zero))))))) ∷ lookup (lookup M (suc (suc zero))) (suc (suc (suc (suc (suc (suc zero)))))) ∷ lookup (lookup M (suc (suc (suc zero)))) (suc (suc (suc (suc (suc zero))))) ∷ lookup (lookup M (suc (suc (suc (suc zero))))) (suc (suc (suc (suc zero)))) ∷ lookup (lookup M (suc (suc (suc (suc (suc zero)))))) (suc (suc (suc zero))) ∷ lookup (lookup M (suc (suc (suc (suc (suc (suc zero))))))) (suc (suc zero)) ∷ lookup (lookup M (suc (suc (suc (suc (suc (suc (suc zero)))))))) (suc zero) ∷ lookup (lookup M (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) zero ∷ [])

magicConstant369 : ℕ
magicConstant369 = 369

euler-row-magic : rowSum superpose zero ≡ magicConstant369 × rowSum superpose (suc zero) ≡ magicConstant369 × rowSum superpose (suc (suc zero)) ≡ magicConstant369 × rowSum superpose (suc (suc (suc zero))) ≡ magicConstant369 × rowSum superpose (suc (suc (suc (suc zero)))) ≡ magicConstant369 × rowSum superpose (suc (suc (suc (suc (suc zero))))) ≡ magicConstant369 × rowSum superpose (suc (suc (suc (suc (suc (suc zero)))))) ≡ magicConstant369 × rowSum superpose (suc (suc (suc (suc (suc (suc (suc zero))))))) ≡ magicConstant369 × rowSum superpose (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ magicConstant369
euler-row-magic = refl , refl , refl , refl , refl , refl , refl , refl , refl

euler-col-magic : colSum superpose zero ≡ magicConstant369 × colSum superpose (suc zero) ≡ magicConstant369 × colSum superpose (suc (suc zero)) ≡ magicConstant369 × colSum superpose (suc (suc (suc zero))) ≡ magicConstant369 × colSum superpose (suc (suc (suc (suc zero)))) ≡ magicConstant369 × colSum superpose (suc (suc (suc (suc (suc zero))))) ≡ magicConstant369 × colSum superpose (suc (suc (suc (suc (suc (suc zero)))))) ≡ magicConstant369 × colSum superpose (suc (suc (suc (suc (suc (suc (suc zero))))))) ≡ magicConstant369 × colSum superpose (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) ≡ magicConstant369
euler-col-magic = refl , refl , refl , refl , refl , refl , refl , refl , refl

euler-diag-magic : diagSum superpose ≡ magicConstant369 × antidiagSum superpose ≡ magicConstant369
euler-diag-magic = refl , refl

-- 幻常数代数: 每行含 {0..8} 各一次, Σ=36, 故 9·36 + 36 + 9 = 369
sum0to8 : 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 ≡ 36
sum0to8 = refl
euler-magic-formula : 9 * 36 + 36 + 9 ≡ 369
euler-magic-formula = refl

-- 0 postulate.
