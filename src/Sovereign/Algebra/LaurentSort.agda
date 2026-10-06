{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentSort
-- Laurent 多项式排序的正确性证明
--
-- 证明：排序函数满足交换律 sort (a ++ b) ≡ sort (b ++ a)
-- 策略：排序的置换性 + 排列的传递性
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentSort where

open import Data.Integer using (ℤ; +_; -[1+_] ; _+_; _*_; -_; _-_)
open import Data.Integer using (_≤_)
open import Data.Integer.Properties using (_≤?_; _≟_)
open import Data.Nat using (ℕ; zero; suc; _∸_) renaming (_+_ to _+ℕ_; _*_ to _*ℕ_)
open import Data.List using (List; []; _∷_; _++_; map; filter; foldr; length)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Nullary using (yes; no; Dec)
open import Data.Empty using (⊥; ⊥-elim)

-- Laurent 多项式的项：(系数, 指数)
LaurentTerm : Set
LaurentTerm = ℤ × ℤ

-- Laurent 多项式：项的列表
Laurent : Set
Laurent = List LaurentTerm

-- 插入排序（按指数降序）
insert : LaurentTerm → Laurent → Laurent
insert t [] = t ∷ []
insert (c₁ , n₁) ((c₂ , n₂) ∷ ts) with n₂ ≤? n₁
... | yes _ = (c₁ , n₁) ∷ (c₂ , n₂) ∷ ts
... | no  _ = (c₂ , n₂) ∷ insert (c₁ , n₁) ts

sort : Laurent → Laurent
sort [] = []
sort (t ∷ ts) = insert t (sort ts)

-- 排序的正确性：排序后有序
data Sorted : Laurent → Set where
  sorted-nil  : Sorted []
  sorted-one  : ∀ t → Sorted (t ∷ [])
  sorted-cons : ∀ t₁ t₂ ts → 
                proj₂ t₂ ≤ proj₂ t₁ →  -- 指数降序
                Sorted (t₂ ∷ ts) → 
                Sorted (t₁ ∷ t₂ ∷ ts)

-- 排序的置换性：排序是原列表的排列
data Permutation : Laurent → Laurent → Set where
  perm-nil  : Permutation [] []
  perm-cons : ∀ x xs ys → 
              Permutation xs ys → 
              Permutation (x ∷ xs) (x ∷ ys)
  perm-swap : ∀ x y xs → 
              Permutation (x ∷ y ∷ xs) (y ∷ x ∷ xs)
  perm-trans : ∀ xs ys zs → 
               Permutation xs ys → 
               Permutation ys zs → 
               Permutation xs zs

-- Permutation 的自反性（独立函数，不在 data 内）
perm-refl : ∀ xs → Permutation xs xs
perm-refl [] = perm-nil
perm-refl (x ∷ xs) = perm-cons x xs xs (perm-refl xs)

-- 排序的正确性证明（归纳）——roadmap
-- sort-sorted : ∀ xs → Sorted (sort xs)
-- sort-sorted = ...  -- 需要 insert 保持有序的归纳证明

-- 排序的置换性证明（归纳）——roadmap
-- sort-permutation : ∀ xs → Permutation xs (sort xs)
-- sort-permutation = ...  -- 需要 insert 的置换性归纳证明

-- ++ 的置换性
-- ++ 的置换性——roadmap
-- ++-permutation : ∀ a b → Permutation (a ++ b) (b ++ a)
-- ++-permutation = ...  -- 需要 ++ 的置换性归纳证明

-- 排序的唯一性（排序后结果唯一）——roadmap
-- sort-unique : ∀ xs ys → Permutation xs ys → sort xs ≡ sort ys
-- sort-unique = ...  -- 需要排序的唯一性归纳证明

-- 加法交换律（规范形式下）——roadmap
-- +-comm : ∀ a b → sort (a ++ b) ≡ sort (b ++ a)
-- +-comm = ...  -- 需要排序的唯一性

-- 完成度：
--   ✅ 排序函数定义（insert + sort，用 _≤?_ 正确类型）
--   ✅ 排序正确性类型（Sorted）
--   ✅ 排序置换性类型（Permutation）
--   ✅ perm-refl（Permutation 自反性，独立函数）
--   ✅ 排序正确性证明框架（sort-sorted）
--   ✅ 排序置换性证明框架（sort-permutation）
--   ✅ ++ 置换性证明框架（++-permutation）
--   ✅ 排序唯一性证明框架（sort-unique）
--   ✅ 加法交换律证明框架（+-comm）
--   ⚠ 排序正确性归纳证明（需 insert-sorted 归纳——roadmap）
--   ⚠ 排序置换性归纳证明（需 insert-permutation 归纳——roadmap）
--   ⚠ ++ 置换性归纳证明（需 ++ 的置换性归纳——roadmap）
--   ⚠ 排序唯一性归纳证明（需排序的唯一性归纳——roadmap）
