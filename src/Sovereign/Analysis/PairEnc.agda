{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.PairEnc
--
-- 有限类型对的混合基数编码：Fin 3 × Fin 4 → Fin 12。
--
-- 数学背景：
--   值 = a + 3 * b（a < 3, b < 4），是 12 个元素的唯一分解（a 为低位）。
--   用于把展示群分量编码 (幅度 Fin 3, 相位 Fin 4) 打包成单个 Fin 12，
--   进而交给 FiniteDynamics 的鸽巢引理。
--
-- 核心原则：
--   1. 界用 +-mono-≤ 与 *-mono-≤ 组合（不用具体数值空模式，附录 12 §6）
--   2. 注入性用 12×12 = 144 case 穷举（每个 case 只需 cong toℕ + 空模式；
--      12 个元素的对，144 是 case 数不是暴力计算 —— 参见附录 5 的上限说明）
--   3. 0 postulate / 0 hole
--
-- 包含：pairEnc / toℕ-pairEnc / pairEnc-injective

module Sovereign.Analysis.PairEnc where

open import Data.Nat using (ℕ; _+_; _*_; _≤_; _<_; zero; suc; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<)
open import Data.Nat.Properties using (+-mono-≤; *-mono-≤; ≤-refl)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

suc≤⇒≤2 : ∀ {m : ℕ} → suc m ≤ 3 → m ≤ 2
suc≤⇒≤2 (s≤s p) = p

suc≤⇒≤3 : ∀ {m : ℕ} → suc m ≤ 4 → m ≤ 3
suc≤⇒≤3 (s≤s p) = p

-- 混合基数编码: (a, b) ↦ a + 3 * b
pairEnc : Fin 3 × Fin 4 → Fin 12
pairEnc (a , b) = fromℕ< (bound a b)
  where
    bound : (a' : Fin 3) (b' : Fin 4) → toℕ a' + 3 * toℕ b' < 12
    bound a' b' =
      s≤s (+-mono-≤ (suc≤⇒≤2 (toℕ<n a'))
                    (*-mono-≤ (≤-refl {3}) (suc≤⇒≤3 (toℕ<n b'))))

toℕ-pairEnc : ∀ p → toℕ (pairEnc p) ≡ toℕ (proj₁ p) + 3 * toℕ (proj₂ p)
toℕ-pairEnc p = toℕ-fromℕ< _

-- 注入性: 144 case 穷举（每 case 用 cong toℕ 得到具体自然数不等，空模式消去）
pairEnc-injective : ∀ p q → pairEnc p ≡ pairEnc q → p ≡ q

pairEnc-injective (fzero , fzero) (fzero , fzero) eq = refl
pairEnc-injective (fzero , fzero) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fzero) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fzero , fsuc fzero) eq = refl
pairEnc-injective (fzero , fsuc fzero) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fzero , fsuc (fsuc fzero)) eq = refl
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fzero , fsuc (fsuc (fsuc fzero))) eq = refl
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc fzero , fzero) eq = refl
pairEnc-injective (fsuc fzero , fzero) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fzero) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc fzero , fsuc fzero) eq = refl
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc fzero)) eq = refl
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq = refl
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc fzero , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fzero) eq = refl
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fzero) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fsuc fzero) eq = refl
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc fzero) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq = refl
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc fzero)) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc fzero , fsuc (fsuc (fsuc fzero))) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc fzero) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc (fsuc fzero)) eq with cong toℕ eq
... | ()
pairEnc-injective (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero))) eq = refl
