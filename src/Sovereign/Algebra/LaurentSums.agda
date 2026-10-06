{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentSums
-- Laurent 项列表的逐指数系数和（sums）及其在规范化插入下的不变量。
--
-- 数学背景：sums u p = 项列表 p 中所有指数等于 exp u 的项的系数之和
-- （ℤ 加法）。规范化插入 insertCᵌ（LaurentNorm）的核心不变量：
--   sums u (insertCᵌ 结果) ≡ sums u ts + sums u (t ∷ [])
-- 插入项 t 的贡献 = sums u (t ∷ [])（单一项列表的和）。
-- 该不变量 + canon-unique（LaurentCanon）⟹ 规范形交换律，⟹ 逐点分配律。
--
-- 证明策略（Round-14 定型）：
--   前插/后插分支：sums-++（拼接可加性）+ +-comm——无 case 分析；
--   合并分支（eq3）：ℤ-ring solver（逐 u≟x 情形）；
--   消去分支（eq-zero）：bt-cancel/bt-exeq（LaurentNorm 的 BTail 字段）
--   逐 u≟t/u≟x 情形 + identity 链。
--
-- ℤ 算术全部复用 stdlib。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentSums where

open import Data.Integer using (ℤ; _≤_; _<_; +_; _+_)
open import Data.Integer.Properties
  using (_≟_; _<?_; _≤?_; ≤-antisym; <-trans; <-irrefl; ≰⇒>;
         +-assoc; +-comm; +-identityˡ; +-identityʳ)
open import Data.Integer.Solver
open Data.Integer.Solver.+-*-Solver
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; canon-nil; canon-one; canon-cons;
         canon-tail; canon-<-head; InT; here; there)
open import Sovereign.Algebra.LaurentNorm
  using (insertCᵌ; Cmp3; cmp3; lt3; eq3; gt3; BTail)

-- ────────────────────────────────────────────────────────────────────
-- sums：逐指数系数和
-- ────────────────────────────────────────────────────────────────────

sums : LaurentTerm → Laurent → ℤ
sums u [] = + 0
sums u ((c , n) ∷ ts) with proj₂ u ≟ n
... | yes _ = c + sums u ts
... | no _  = sums u ts

-- 可加性：拼接的和 = 和的和
sums-++ : ∀ (u : LaurentTerm) xs ys →
  sums u (xs ++ ys) ≡ sums u xs + sums u ys
sums-++ u [] ys = sym (+-identityˡ (sums u ys))
sums-++ u ((c , n) ∷ xs) ys with proj₂ u ≟ n
... | yes _ =
  trans (cong (λ w → c + w) (sums-++ u xs ys))
        (sym (+-assoc c (sums u xs) (sums u ys)))
... | no _ = sums-++ u xs ys

-- ────────────────────────────────────────────────────────────────────
-- 核心引理：插入保持逐指数和（对 Canon 结构归纳）
-- 不变量：sums u (插入结果) ≡ sums u ts + sums u (t ∷ [])
-- ────────────────────────────────────────────────────────────────────

insertCᵌ-sums : ∀ (u t : LaurentTerm) ts (c : Canon ts) →
  sums u (proj₁ (insertCᵌ t ts c)) ≡ sums u ts + sums u (t ∷ [])
insertCᵌ-sums u t [] c =
  sym (+-identityˡ (sums u (t ∷ [])))

-- 单元素分支
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g =
  -- 结果 = t ∷ (x ∷ []) = (t ∷ []) ++ (x ∷ [])：sums-++ + comm
  trans (sums-++ u (t ∷ []) (x ∷ []))
        (+-comm (sums u (t ∷ [])) (sums u (x ∷ [])))
... | lt3 _ _ l =
  -- 结果 = x ∷ (t ∷ []) = (x ∷ []) ++ (t ∷ [])：sums-++ + comm
  trans (sums-++ u (x ∷ []) (t ∷ []))
        (+-comm (sums u (x ∷ [])) (sums u (t ∷ [])))

-- 双元素及以上分支
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g =
  -- 结果 = t ∷ (x ∷ x₂ ∷ xs) = (t ∷ []) ++ (x ∷ x₂ ∷ xs)：sums-++ + comm
  trans (sums-++ u (t ∷ []) (x ∷ x₂ ∷ xs))
        (+-comm (sums u (t ∷ [])) (sums u (x ∷ x₂ ∷ xs)))

-- 合并分支（eq3）：结果封闭 = m ∷ (x₂ ∷ xs)，逐 u≟x 情形 + solver
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | eq3 _ _ e with proj₂ u ≟ proj₂ x
...   | yes ux =
  -- LHS = (proj₁ t + proj₁ x) + sums u (x₂ ∷ xs)
  -- RHS = (proj₂ x + sums u (x₂ ∷ xs)) + (proj₂ t + + 0)
  --   （ux-yes：proj₂ u ≡ proj₂ x；e：proj₂ t ≡ proj₂ x）
  solve 3 (λ S a b → S + (a + b) := (b + S) + (a + con (+ 0)))
          refl (sums u (x₂ ∷ xs)) (proj₂ t) (proj₂ x)
...   | no ux =
  -- ux-no：exp u ≢ exp x（e）⟹ exp u ≢ exp m ⟹ LHS = sums u (x₂ ∷ xs)
  -- RHS = sums u (x₂ ∷ xs) + (+ 0 + + 0)
  trans (sym (+-identityʳ (sums u (x₂ ∷ xs))))
        (trans (cong (λ w → w + sums u (x₂ ∷ xs)) (sym (+-identityˡ (+ 0))))
               (trans (cong (λ w → w + (+ 0 + + 0)) (sym (+-identityʳ (+ 0))))
                      refl))

-- 消去分支（eq-zero）：bt-cancel/bt-exeq 逐 u≟t/u≟x 情形
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes z with proj₂ u ≟ proj₂ t | proj₂ u ≟ proj₂ x
  -- LHS = sums u (x₂ ∷ xs)；RHS = sums u (x ∷ …) + sums u (t ∷ [])
  --     = (proj₁ x + sums u (x₂ ∷ xs)) + (proj₁ t + + 0)
  -- bt-cancel : proj₁ t + proj₁ x ≡ + 0 ⟹ proj₁ x + proj₁ t ≡ + 0
  --   ⟹ RHS ≡ sums u (x₂ ∷ xs) + + 0 ≡ LHS
  trans (sym (+-identityʳ (sums u (x₂ ∷ xs))))
        (trans (cong (λ w → (w + sums u (x₂ ∷ xs)) + (proj₁ t + + 0))
                          (sym (trans (+-comm (proj₁ t) (proj₁ x)) (sym z))))
               (sym (trans (+-assoc (proj₁ x) (proj₁ t) (+ 0))
                           (+-identityʳ (proj₁ x + proj₁ t)))))
...     | yes pt | no px = ⊥-elim (px (trans pt (sym e)))
...     | no pt | yes px = ⊥-elim (pt (trans (sym px) e))
...     | no pt | no px =
  -- LHS = sums u (x₂ ∷ xs)；RHS = sums u (x₂ ∷ xs) + + 0
  trans (sym (+-identityʳ (sums u (x₂ ∷ xs))))
        (trans (cong (λ w → w + (+ 0 + + 0)) (sym (+-identityˡ (+ 0))))
               refl)

-- 后插分支组装（sums-++ + 内层 IH）
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | lt3 _ _ l with insertCᵌ t (x₂ ∷ xs) s
...   | (w' , cw' , dj') =
  trans (sums-++ u (x ∷ []) (proj₁ (insertCᵌ t (x₂ ∷ xs) s)))
        (trans (cong (λ w → proj₁ x + w)
                     (insertCᵌ-sums u t (x₂ ∷ xs) s))
               (sym (+-assoc (proj₁ x) (sums u (x₂ ∷ xs))
                             (sums u (t ∷ [])))))
