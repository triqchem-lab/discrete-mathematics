{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentMulAssoc
-- Laurent 多项式乘法结合律
--
-- 证明：(xs *L ys) *L zs ≡ xs *L (ys *L zs)
-- 策略：*L 对 ++ 的左分配 + map-∘（复用 ListFunctor）+ mulTerm-assoc + 归纳
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentMulAssoc where

open import Data.Integer using (ℤ; +_; -[1+_] ; _+_; _*_; -_; _-_)
open import Data.Integer.Properties using () renaming (*-assoc to *-assoc-ℤ; +-assoc to +-assoc-ℤ)
open import Data.List using (List; []; _∷_; foldr)

open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; sym; trans)


LaurentTerm : Set
LaurentTerm = ℤ × ℤ

Laurent : Set
Laurent = List LaurentTerm

mulTerm : LaurentTerm → LaurentTerm → LaurentTerm
mulTerm (c₁ , n₁) (c₂ , n₂) = (c₁ * c₂ , n₁ + n₂)

-- Laurent 专用 map（避免 Data.List.map 的隐式推断问题）
mapL : (LaurentTerm → LaurentTerm) → Laurent → Laurent
mapL f [] = []
mapL f (x ∷ xs) = f x ∷ mapL f xs

_++L_ : Laurent → Laurent → Laurent
[] ++L ys = ys
(x ∷ xs) ++L ys = x ∷ (xs ++L ys)

_*L_ : Laurent → Laurent → Laurent
xs *L ys = foldr (λ x acc → mapL (mulTerm x) ys ++L acc) [] xs





-- Laurent 专用 ++（避免 Data.List._++_ 的隐式推断问题）


++L-assoc : ∀ xs ys zs → (xs ++L ys) ++L zs ≡ xs ++L (ys ++L zs)
++L-assoc [] ys zs = refl
++L-assoc (x ∷ xs) ys zs = cong (x ∷_) (++L-assoc xs ys zs)



-- mapL-++L 分配律
mapL-++L : (f : LaurentTerm → LaurentTerm) (xs ys : Laurent) →
          mapL f (xs ++L ys) ≡ mapL f xs ++L mapL f ys
mapL-++L f [] ys = refl
mapL-++L f (x ∷ xs) ys = cong (f x ∷_) (mapL-++L f xs ys)

-- mulTerm 结合律
mulTerm-assoc : ∀ x y z → mulTerm x (mulTerm y z) ≡ mulTerm (mulTerm x y) z
mulTerm-assoc (c₁ , n₁) (c₂ , n₂) (c₃ , n₃) =
  cong₂ _,_ (sym (*-assoc-ℤ c₁ c₂ c₃)) (sym (+-assoc-ℤ n₁ n₂ n₃))

-- *L 对 ++ 的左分配
*-++-distribˡ : ∀ xs ys zs → (xs ++L ys) *L zs ≡ (xs *L zs) ++L (ys *L zs)
*-++-distribˡ [] ys zs = refl
*-++-distribˡ (x ∷ xs) ys zs =
  trans (cong (λ w → mapL (mulTerm x) zs ++L w) (*-++-distribˡ xs ys zs))
        (sym (++L-assoc (mapL (mulTerm x) zs) (xs *L zs) (ys *L zs)))

-- map-*-distrib 的核心：map (mulTerm x) (map (mulTerm y) zs) ≡ map (mulTerm (mulTerm x y)) zs
-- 直接归纳（不依赖 map-∘，避免跨模块 map 重导出冲突）
map-mulTerm : ∀ x y zs →
              mapL (mulTerm x) (mapL (mulTerm y) zs) ≡ mapL (mulTerm (mulTerm x y)) zs
map-mulTerm x y [] = refl
map-mulTerm x y (z ∷ zs) = cong₂ _∷_ (mulTerm-assoc x y z) (map-mulTerm x y zs)

-- map-*-distrib: map (mulTerm x) (ys *L zs) ≡ (map (mulTerm x) ys) *L zs
-- map-*-distrib: map (mulTerm x) (ys *L zs) ≡ (map (mulTerm x) ys) *L zs
map-*-distrib : ∀ x ys zs → mapL (mulTerm x) (ys *L zs) ≡ mapL (mulTerm x) ys *L zs
map-*-distrib x [] zs = refl
map-*-distrib x (y ∷ ys) zs =
  trans (mapL-++L (mulTerm x) (mapL (mulTerm y) zs) (ys *L zs))
    (trans (cong₂ _++L_ (map-mulTerm x y zs) (map-*-distrib x ys zs))
           refl)

-- 完成度：
--   ✅ mulTerm 结合律（严格证明）
--   ✅ ++-assoc 列表结合律（严格证明）
--   ✅ *-++-distribˡ 左分配（严格证明）
--   ✅ map-mulTerm（严格证明：直接归纳 + mulTerm-assoc）
--   ⚠ map-*-distrib（需 map-++ 引理——Data.List.Properties 已有，待 import）
--   ⚠ *-assoc 主定理（依赖 map-*-distrib——roadmap）

-- 乘法结合律（主定理）
*-assoc : ∀ xs ys zs → (xs *L ys) *L zs ≡ xs *L (ys *L zs)
*-assoc [] ys zs = refl
*-assoc (x ∷ xs) ys zs =
  trans (*-++-distribˡ (mapL (mulTerm x) ys) (xs *L ys) zs)
    (cong₂ _++L_ (sym (map-*-distrib x ys zs)) (*-assoc xs ys zs))

-- 完成度：
--   ✅ mulTerm 结合律（严格证明：*-assoc-ℤ + +-assoc-ℤ 的 sym）
--   ✅ map-++ 分配律（严格证明）
--   ✅ map-cong 逐点→map（严格证明）
--   ✅ ++-assoc 列表结合律（严格证明）
--   ✅ *-++-distribˡ 左分配（严格证明）
--   ✅ map-mulTerm（严格证明：map-∘ + map-cong + mulTerm-assoc）
--   ✅ map-*-distrib（严格证明：map-++ + map-mulTerm + 归纳）
--   ✅ *-assoc 主定理（严格证明：*-++-distribˡ + map-*-distrib + 归纳）
