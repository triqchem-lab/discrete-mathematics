{-# OPTIONS --rewriting --guardedness #-}

-- | _PSU（Laurent.sort-unique 拼装探针）
-- 数学背景：排序/规范形的唯一性。⚠ 任务书原签名
--   `xs ↭ ys → sort xs ≡ sort ys`（裸插入排序）**为假**——等指数异系数项的
--   插入序决定输出（tie 反例见下）。真命题 = **Canon 输出前提下**的唯一性
--   （指数互异 ⟹ 排序由内容决定）：恰为 sort-perm 链 + canon-unique 收口。
-- 交付三件：canon-unique-↭（核心收口）/ sort-unique（修正版）/ sort-unique-tie-false（反证）。
module _PSU where

open import Data.Integer using (ℤ; _<_; _≤_; +_)
open import Data.Integer.Base using (+<+)
open import Data.Nat using (z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-sym; refl; prep; swap) renaming (trans to ↭-t)
open import Sovereign.Algebra.LaurentSort using (sort; sort-perm)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; InT; In-resp-↭; canon-unique;
         canon-nil; canon-one; canon-cons)

-- ────────────────────────────────────────────────────────────────────
-- 1. 核心收口件：置换 + 双 Canon ⟹ 逐点相等
--   成员双向转移由 In-resp-↭ 及其对称给出，canon-unique 直接收口
-- ────────────────────────────────────────────────────────────────────

canon-unique-↭ : ∀ {xs ys : Laurent} → Canon xs → Canon ys → xs ↭ ys → xs ≡ ys
canon-unique-↭ {xs} {ys} cx cy p =
  canon-unique xs ys cx cy (In-resp-↭ p) (In-resp-↭ (↭-sym p))

-- ────────────────────────────────────────────────────────────────────
-- 2. sort-unique（修正版）：置换等价 + 双侧 Canon 输出 ⟹ sort 相等
--   装配链：sort xs ↭ xs ↭ ys ↭ sort ys（sort-perm 双向 + ↭-trans）
--          → canon-unique-↭ 收口
-- ────────────────────────────────────────────────────────────────────

sort-unique : ∀ (xs ys : Laurent) → xs ↭ ys
  → Canon (sort xs) → Canon (sort ys) → sort xs ≡ sort ys
sort-unique xs ys p cxs cys = canon-unique-↭ cxs cys sort-chain
  where
  -- sort xs ↭ xs ↭ ys ↭ sort ys  [排序是置换，三段拼接]
  sort-chain : sort xs ↭ sort ys
  sort-chain = ↭-t (↭-t (↭-sym (sort-perm xs)) p) (sort-perm ys)

-- ────────────────────────────────────────────────────────────────────
-- 3. 反证件：任务书原签名（无 Canon 前提）为假
--   tie 反例：a=(1,0), b=(2,0)（同指数、异系数）
--   sort [a,b] = [a,b]，sort [b,a] = [b,a]（插入序保留），而 [a,b] ↭ [b,a]
-- ────────────────────────────────────────────────────────────────────

a b : LaurentTerm
a = (+ 1) , (+ 0)
b = (+ 2) , (+ 0)

tie-xs tie-ys : Laurent
tie-xs = a ∷ b ∷ []
tie-ys = b ∷ a ∷ []

tie-perm : tie-xs ↭ tie-ys
tie-perm = swap a b refl

sort-tie-xs : sort tie-xs ≡ a ∷ b ∷ []
sort-tie-xs = refl

sort-tie-ys : sort tie-ys ≡ b ∷ a ∷ []
sort-tie-ys = refl

-- 首项系数提取（区分 a,b）
cf : Laurent → ℤ
cf [] = + 0
cf (x ∷ _) = proj₁ x

1≢2 : (+ 1) ≢ (+ 2)
1≢2 ()

sort-unique-tie-false : ¬ (∀ (xs ys : Laurent) → xs ↭ ys → sort xs ≡ sort ys)
sort-unique-tie-false claim = 1≢2 (cong cf raw)
  where
  -- [a,b] ≡ sort [a,b] ≡ sort [b,a] ≡ [b,a]  [任务书断言 + refl 计算]
  raw : a ∷ b ∷ [] ≡ b ∷ a ∷ []
  raw = trans (sym sort-tie-xs) (trans (claim tie-xs tie-ys tie-perm) sort-tie-ys)

-- ────────────────────────────────────────────────────────────────────
-- 4. 小例交叉（验证点②）：指数互异例走 sort-unique 真通道
-- ────────────────────────────────────────────────────────────────────

s1 s2 : Laurent
s1 = ((+ 1) , (+ 2)) ∷ ((+ 3) , (+ 1)) ∷ []
s2 = ((+ 3) , (+ 1)) ∷ ((+ 1) , (+ 2)) ∷ []

s1↭s2 : s1 ↭ s2
s1↭s2 = swap ((+ 1) , (+ 2)) ((+ 3) , (+ 1)) refl

check-sort : sort s1 ≡ sort s2
check-sort = refl

1<2 : (+ 1) < (+ 2)
1<2 = +<+ (s≤s (s≤s z≤n))

c-s1 : Canon (sort s1)
c-s1 = canon-cons ((+ 1) , (+ 2)) ((+ 3) , (+ 1)) [] 1<2 (canon-one ((+ 3) , (+ 1)))

c-s2 : Canon (sort s2)
c-s2 = canon-cons ((+ 1) , (+ 2)) ((+ 3) , (+ 1)) [] 1<2 (canon-one ((+ 3) , (+ 1)))

check-unique : sort s1 ≡ sort s2
check-unique = sort-unique s1 s2 s1↭s2 c-s1 c-s2
