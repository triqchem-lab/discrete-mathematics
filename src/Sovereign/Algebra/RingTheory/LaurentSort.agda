{-# OPTIONS --rewriting --guardedness #-}

-- ⚠️ [HISTORICAL 2026-10-10 人类裁决] List 表示路线已冻结：唯一主路线 = 函数表示 LaurentCubical（funExt 直接得函数相等）。本模块不再投入新工作；下游请迁移到 LaurentCubical。
-- | Sovereign.Algebra.RingTheory.LaurentSort
-- Laurent 多项式排序规范化的正确性：排序保持置换不变量、且结果有序。
--
-- 数学背景：Z[t,t⁻¹] 的项用裸 List (ℤ × ℤ) 表示（未排序、不去重），
-- 逐点相等的分配律不成立（见 LaurentDistrib 的反例 not-distrib-pointwise），
-- 真命题是模置换相等 ↭。排序规范化是把「模置换」变成「逐点相等」的第一步：
-- 若 sort 是良定义的规范化函数且 sort (a ++ b) ≡ sort (b ++ a)，
-- 则范化后的环公理可逐点陈述。
--
-- 本模块完成（0 postulate / 0 hole）：
--   1. insert-perm / sort-perm   ：排序不丢信息（是原列表的置换）
--   2. insert-sorted / sort-sorted：排序结果按指数降序有序
--   3. ++-comm-↭                 ：列表拼接的置换交换律（直接复用 stdlib）
--
-- 设计决策（2026-10）：手写 Permutation data 换成 stdlib _↭_——
-- stdlib 有丰富的 congruence 引理（++⁺ˡ/++⁺ʳ/++-comm/++-assoc），
-- 手写 data 缺 congruence 会把 ++ 交换律的证明卡死。
-- insert 的分支改用 _<?_（严格小于）决策：no 分支给的是构造性信息
-- ¬(n₁ < n₂)，经 ≰⇒> 反转得到排序所需的 n₂ ≤ n₁。
module Sovereign.Algebra.RingTheory.LaurentSort where

open import Data.Integer
  using (ℤ; _≤_; _<_)
open import Data.Integer.Properties
  using (_≤?_; _<?_; ≤-refl; ≤-trans; <⇒≤; ≰⇒>)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥-elim)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; refl; prep; swap; trans)
open import Data.List.Relation.Binary.Permutation.Propositional.Properties
  using (↭-trans; ++-comm)

-- Laurent 多项式的项：(系数, 指数)
LaurentTerm : Set
LaurentTerm = ℤ × ℤ

-- Laurent 多项式：项的列表
Laurent : Set
Laurent = List LaurentTerm

-- ────────────────────────────────────────────────────────────────────
-- 插入排序（按指数降序）
-- 分支用 _<?_：no 分支给出 ¬(n₁ < n₂)，用于有界性反转
-- ────────────────────────────────────────────────────────────────────

insert : LaurentTerm → Laurent → Laurent
insert t [] = t ∷ []
insert (c₁ , n₁) ((c₂ , n₂) ∷ ts) with n₁ <? n₂
... | no  _ = (c₁ , n₁) ∷ ((c₂ , n₂) ∷ ts)
... | yes _ = (c₂ , n₂) ∷ insert (c₁ , n₁) ts

sort : Laurent → Laurent
sort [] = []
sort (t ∷ ts) = insert t (sort ts)

-- ────────────────────────────────────────────────────────────────────
-- 第一部分：置换不变量（排序不丢信息）
-- ────────────────────────────────────────────────────────────────────

-- 插入是置换：(t ∷ ts) ↭ (insert t ts)
-- 证明：对 ts 归纳。yes 分支 = swap + prep(归纳假设)。
insert-perm : ∀ t ts → (t ∷ ts) ↭ insert t ts
insert-perm t [] = refl
insert-perm (c₁ , n₁) ((c₂ , n₂) ∷ ts) with n₁ <? n₂
... | no  _ = refl
... | yes _ =
  trans (swap (c₁ , n₁) (c₂ , n₂) refl)
        (prep (c₂ , n₂) (insert-perm (c₁ , n₁) ts))

-- 排序是置换：xs ↭ sort xs
sort-perm : ∀ xs → xs ↭ sort xs
sort-perm [] = refl
sort-perm (x ∷ xs) =
  trans (prep x (sort-perm xs)) (insert-perm x (sort xs))

-- 拼接的置换交换律：直接复用 stdlib ++-comm
++-comm-↭ : ∀ (a b : Laurent) → (a ++ b) ↭ (b ++ a)
++-comm-↭ = ++-comm

-- ────────────────────────────────────────────────────────────────────
-- 第二部分：有序性（排序结果按指数降序）
-- ────────────────────────────────────────────────────────────────────

data Sorted : Laurent → Set where
  sorted-nil  : Sorted []
  sorted-one  : ∀ t → Sorted (t ∷ [])
  sorted-cons : ∀ t₁ t₂ ts →
                proj₂ t₂ ≤ proj₂ t₁ →   -- 指数降序
                Sorted (t₂ ∷ ts) →
                Sorted (t₁ ∷ t₂ ∷ ts)

-- 非空有序列表的尾部有序
sorted-tail : ∀ {t ts} → Sorted (t ∷ ts) → Sorted ts
sorted-tail (sorted-one t) = sorted-nil
sorted-tail (sorted-cons t₁ t₂ ts p s) = s

-- 序反转：¬(n₂ ≤ n₁) → n₁ < n₂（stdlib ≰⇒> 的方向换算）
¬≤⇒< : ∀ n₁ n₂ → ¬ (n₂ ≤ n₁) → n₁ < n₂
¬≤⇒< n₁ n₂ h = ≰⇒> h

-- 插入的组合性质（真不变量）：插入结果 = h ∷ r，且
--   (a) 有序，(b) 首项指数 ≤ t，或 ≤ ts 的首项（yes 分支时首项来自 ts）。
-- 上一版把 (b) 写死成「≤ t」是陈述错误：yes 分支首项来自 ts，可大于 t。
insert-prop : ∀ t ts → Sorted ts →
  Σ LaurentTerm (λ h → Σ Laurent (λ r →
     (insert t ts ≡ h ∷ r)
     × Sorted (h ∷ r)
     × ((proj₂ h ≤ proj₂ t)
        ⊎ (Σ LaurentTerm (λ x → Σ Laurent (λ xs' →
             (ts ≡ x ∷ xs') × (proj₂ h ≤ proj₂ x)))))))
insert-prop t [] s = t , [] , refl , sorted-one t , inj₁ ≤-refl
insert-prop (c₁ , n₁) ((c₂ , n₂) ∷ ts) s with n₁ <? n₂
... | no  n₁≮n₂ =
  (c₁ , n₁) , ((c₂ , n₂) ∷ ts) , refl
      , sorted-cons (c₁ , n₁) (c₂ , n₂) ts (bound n₁≮n₂) s
      , inj₁ ≤-refl
  where
  -- 从 ¬(n₁ < n₂) 反推 n₂ ≤ n₁（用 _≤?_ 的可判定性闭环）
  bound : ¬ (n₁ < n₂) → n₂ ≤ n₁
  bound ¬lt with n₂ ≤? n₁
  ... | yes p = p
  ... | no  q = ⊥-elim (¬lt (¬≤⇒< n₁ n₂ q))
... | yes n₁<n₂ =
  -- rec = (h , r , eq , srt , dj)，用投影取分量（可解构 let 不做定义性展开）
  let rec = insert-prop (c₁ , n₁) ts (sorted-tail s) in
  (c₂ , n₂)
  , insert (c₁ , n₁) ts
  , refl
  , subst Sorted (cong ((c₂ , n₂) ∷_) (sym (proj₁ (proj₂ (proj₂ rec)))))
      (sorted-cons (c₂ , n₂) (proj₁ rec) (proj₁ (proj₂ rec))
        (hle≤n₂ rec n₁<n₂ s)
        (proj₁ (proj₂ (proj₂ (proj₂ rec)))))
  , inj₂ ((c₂ , n₂) , ts , refl , ≤-refl)
  where
  -- 内层首项 h 的指数 ≤ 外层首项 n₂：
  --   左支：h ≤ n₁ < n₂；右支：h ≤ x₀，x₀ ≤ n₂（来自外层有序性）
  -- 有序列表第二项 ≤ 首项
  x₀≤parent : ∀ x₀ xs'' → Sorted ((c₂ , n₂) ∷ x₀ ∷ xs'') → proj₂ x₀ ≤ n₂
  x₀≤parent x₀ xs'' (sorted-cons _ _ _ p _) = p

  hle≤n₂ : (rec : Σ LaurentTerm (λ h → Σ Laurent (λ r →
             (insert (c₁ , n₁) ts ≡ h ∷ r)
             × Sorted (h ∷ r)
             × ((proj₂ h ≤ n₁)
                ⊎ (Σ LaurentTerm (λ x → Σ Laurent (λ xs' →
                     (ts ≡ x ∷ xs') × (proj₂ h ≤ proj₂ x)))))))
         ) → n₁ < n₂ → Sorted ((c₂ , n₂) ∷ ts) → proj₂ (proj₁ rec) ≤ n₂
  hle≤n₂ rec n₁<n₂ s' with proj₂ (proj₂ (proj₂ (proj₂ rec)))
  ... | inj₁ h≤n₁ = ≤-trans h≤n₁ (<⇒≤ n₁<n₂)
  ... | inj₂ (x₀ , xs'' , e , h≤x₀) =
    ≤-trans h≤x₀ (x₀≤parent x₀ xs'' (subst Sorted (cong ((c₂ , n₂) ∷_) e) s'))

-- 插入保持有序
insert-sorted : ∀ t ts → Sorted ts → Sorted (insert t ts)
insert-sorted t ts s with insert-prop t ts s
... | h , r , eq , srt , hle = subst Sorted (sym eq) srt

-- 排序结果有序
sort-sorted : ∀ xs → Sorted (sort xs)
sort-sorted [] = sorted-nil
sort-sorted (x ∷ xs) = insert-sorted x (sort xs) (sort-sorted xs)

-- ────────────────────────────────────────────────────────────────────
-- §sort-unique（拼装批，含 statement_wrong 修正：裸 sort 的 tie 反例）
--   修正版带 Canon 前提（指数互异 = tie 排除条件）；原签名反证件 sort-unique-tie-false 在列
-- ────────────────────────────────────────────────────────────────────

-- | _PSU（Laurent.sort-unique 拼装探针）
-- 数学背景：排序/规范形的唯一性。⚠ 任务书原签名
--   `xs ↭ ys → sort xs ≡ sort ys`（裸插入排序）**为假**——等指数异系数项的
--   插入序决定输出（tie 反例见下）。真命题 = **Canon 输出前提下**的唯一性
--   （指数互异 ⟹ 排序由内容决定）：恰为 sort-perm 链 + canon-unique 收口。
-- 交付三件：canon-unique-↭（核心收口）/ sort-unique（修正版）/ sort-unique-tie-false（反证）。

open import Data.Integer using (ℤ; _<_; _≤_; +_)
open import Data.Integer.Base using (+<+)
open import Data.Nat using (z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality renaming (trans to ≡-t)
  using (_≡_; _≢_; refl; sym; ≡-t; cong)
open import Relation.Nullary using (¬_)
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; ↭-sym; refl; prep; swap) renaming (trans to ↭-t)
open import Sovereign.Algebra.RingTheory.LaurentCanon
  using (Canon; InT; In-resp-↭; canon-unique;
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
--   装配链：sort xs ↭ xs ↭ ys ↭ sort ys（sort-perm 双向 + ↭-≡-t）
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
  raw = ≡-t (sym sort-tie-xs) (≡-t (claim tie-xs tie-ys tie-perm) sort-tie-ys)

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
