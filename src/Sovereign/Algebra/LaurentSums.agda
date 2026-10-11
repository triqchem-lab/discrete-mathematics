{-# OPTIONS --rewriting --guardedness #-}

-- ⚠️ [HISTORICAL 2026-10-10 人类裁决] List 表示路线已冻结：唯一主路线 = 函数表示 LaurentCubical（funExt 直接得函数相等）。本模块不再投入新工作；下游请迁移到 LaurentCubical。
-- | Sovereign.Algebra.LaurentSums
-- Laurent 项列表的逐指数系数和（sums）及其在规范化插入下的不变量。
--
-- 数学背景：sums u p = 项列表 p 中所有指数等于 exp u 的项的系数之和
-- （ℤ 加法）。规范化插入 insertCᵌ（LaurentNorm）的核心不变量：
--   sums u (insertCᵌ 结果) ≡ sums u ts + sums u (t ∷ [])
-- 插入项 t 的贡献 = sums u (t ∷ [])（单一项列表的和）。
--
-- 证明策略（Round-18 Dec-参数定型）：
--   ① sums-cons-head / sums-cons-tail：一步展开引理（显式参数化）；
--   ② 辅助函数用 Dec 参数做情形分析（模式匹配不抽象目标）；
--   ③ 主定理：with cmp3 精炼 insertCᵌ（探针验证），辅助函数闭合算术；
--   ④ 无嵌套 with、无 where、无 mutual。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentSums where

open import Data.Integer using (ℤ; _≤_; _<_; +_; _+_; -_)
open import Data.Integer.Properties
  using (_≟_; _<?_; _≤?_; ≤-antisym; <-trans; <-irrefl; ≰⇒>;
         +-assoc; +-comm; +-identityˡ; +-identityʳ; +-inverseˡ; +-inverseʳ)
open import Data.Integer.Solver
open Data.Integer.Solver.+-*-Solver
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; cong₂; sym; trans; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; canon-nil; canon-one; canon-cons;
         canon-tail; canon-<-head; InT; here; there)
open import Sovereign.Algebra.LaurentNorm
  using (insertCᵌ; Cmp3; cmp3; lt3; eq3; gt3; BTail; SpecT; lt3-cons)

-- ────────────────────────────────────────────────────────────────────
-- sums：逐指数系数和（let-free，case_of_ 替代 with）
-- ────────────────────────────────────────────────────────────────────

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

sums : LaurentTerm → Laurent → ℤ
sums u [] = + 0
sums u ((c , n) ∷ ts) = case proj₂ u ≟ n of λ
  { (yes _) → c + sums u ts
  ; (no _)  → sums u ts
  }

-- 一步展开引理
sums-cons-head : ∀ (u t : LaurentTerm) ts → proj₂ u ≡ proj₂ t →
  sums u (t ∷ ts) ≡ proj₁ t + sums u ts
sums-cons-head u t ts e with proj₂ u ≟ proj₂ t
... | yes _ = refl
... | no q  = ⊥-elim (q e)

sums-cons-tail : ∀ (u t : LaurentTerm) ts → ¬ (proj₂ u ≡ proj₂ t) →
  sums u (t ∷ ts) ≡ sums u ts
sums-cons-tail u t ts h with proj₂ u ≟ proj₂ t
... | yes e = ⊥-elim (h e)
... | no _  = refl

-- 可加性
sums-++ : ∀ (u : LaurentTerm) xs ys →
  sums u (xs ++ ys) ≡ sums u xs + sums u ys
sums-++ u [] ys = sym (+-identityˡ (sums u ys))
sums-++ u ((c , n) ∷ xs) ys with proj₂ u ≟ n
... | yes _ =
  trans (cong (λ w → c + w) (sums-++ u xs ys))
        (sym (+-assoc c (sums u xs) (sums u ys)))
... | no _ = sums-++ u xs ys

-- 零和洗牌：dx + dt ≡ + 0 ⟹ S ≡ (dx + S) + dt
zero-shuffle : ∀ S dx dt → dx + dt ≡ + 0 → S ≡ (dx + S) + dt
zero-shuffle S dx dt z =
  sym (trans (+-assoc dx S dt)
  (trans (cong (λ w → dx + w) (+-comm S dt))
  (trans (sym (+-assoc dx dt S))
  (trans (cong (_+ S) z)
         (+-identityˡ S)))))

-- ────────────────────────────────────────────────────────────────────
-- 辅助函数（Dec 参数做情形分析）
-- ────────────────────────────────────────────────────────────────────

-- 单元素 gt3：结果 = t ∷ (x ∷ [])
one-gt-sums : ∀ u t x → proj₂ x < proj₂ t →
  Dec (proj₂ u ≡ proj₂ t) → Dec (proj₂ u ≡ proj₂ x) →
  sums u (t ∷ (x ∷ [])) ≡ sums u (x ∷ []) + sums u (t ∷ [])
one-gt-sums u t x g (yes pt) (yes px) =
  ⊥-elim (<-irrefl refl
    (subst (λ z → z < proj₂ t) pt (subst (λ z → z < proj₂ t) (sym px) g)))
one-gt-sums u t x g (yes pt) (no px) =
  let lhs-eq = trans (sums-cons-head u t (x ∷ []) pt)
                     (cong (λ w → proj₁ t + w) (sums-cons-tail u x [] px))
      rhs-eq = cong₂ _+_ (sums-cons-tail u x [] px)
                         (sums-cons-head u t [] pt)
  in  trans lhs-eq
      (trans (sym (+-identityˡ (proj₁ t + + 0))) (sym rhs-eq))
one-gt-sums u t x g (no pt) (yes px) =
  let lhs-eq = trans (sums-cons-tail u t (x ∷ []) pt)
                     (sums-cons-head u x [] px)
      rhs-eq = cong₂ _+_ (sums-cons-head u x [] px)
                         (sums-cons-tail u t [] pt)
  in  trans lhs-eq
      (trans (sym (+-identityʳ (proj₁ x + + 0))) (sym rhs-eq))
one-gt-sums u t x g (no pt) (no px) =
  let lhs-eq = trans (sums-cons-tail u t (x ∷ []) pt)
                     (sums-cons-tail u x [] px)
      rhs-eq = cong₂ _+_ (sums-cons-tail u x [] px)
                         (sums-cons-tail u t [] pt)
  in  trans lhs-eq (trans (sym (+-identityˡ (+ 0))) (sym rhs-eq))

-- 单元素 eq3-zero：结果 = []
one-eq-zero-sums : ∀ u t x → proj₂ t ≡ proj₂ x → proj₁ t + proj₁ x ≡ + 0 →
  Dec (proj₂ u ≡ proj₂ t) → Dec (proj₂ u ≡ proj₂ x) →
  sums u [] ≡ sums u (x ∷ []) + sums u (t ∷ [])
one-eq-zero-sums u t x e z (yes pt) (yes px) =
  let rhs-eq = cong₂ _+_ (sums-cons-head u x [] px)
                         (sums-cons-head u t [] pt)
      collapse : (proj₁ x + + 0) + (proj₁ t + + 0) ≡ + 0
      collapse = trans (cong₂ _+_ (+-identityʳ (proj₁ x))
                                  (+-identityʳ (proj₁ t)))
                       (trans (+-comm (proj₁ x) (proj₁ t)) z)
  in  trans (sym collapse) (sym rhs-eq)
one-eq-zero-sums u t x e z (yes pt) (no px) = ⊥-elim (px (trans pt e))
one-eq-zero-sums u t x e z (no pt) (yes px) = ⊥-elim (pt (trans px (sym e)))
one-eq-zero-sums u t x e z (no pt) (no px) =
  let rhs-eq = cong₂ _+_ (sums-cons-tail u x [] px)
                         (sums-cons-tail u t [] pt)
  in  trans (sym (+-identityˡ (+ 0)))
      (trans (sym (+-identityˡ (+ 0))) (sym rhs-eq))

-- 单元素 eq3-nz：结果 = m ∷ []
one-eq-nz-sums : ∀ u t x → proj₂ t ≡ proj₂ x → ¬ (proj₁ t + proj₁ x ≡ + 0) →
  Dec (proj₂ u ≡ proj₂ t) → Dec (proj₂ u ≡ proj₂ x) →
  sums u ((proj₁ t + proj₁ x , proj₂ t) ∷ []) ≡ sums u (x ∷ []) + sums u (t ∷ [])
one-eq-nz-sums u t x e nz (yes pt) (yes px) =
  let lhs-eq = sums-cons-head u (proj₁ t + proj₁ x , proj₂ t) [] pt
      rhs-eq = cong₂ _+_ (sums-cons-head u x [] px)
                         (sums-cons-head u t [] pt)
  in  trans lhs-eq
      (trans (trans (+-identityʳ (proj₁ t + proj₁ x))
             (trans (+-comm (proj₁ t) (proj₁ x))
                    (sym (cong₂ _+_ (+-identityʳ (proj₁ x))
                                    (+-identityʳ (proj₁ t))))))
             (sym rhs-eq))
one-eq-nz-sums u t x e nz (yes pt) (no px) = ⊥-elim (px (trans pt e))
one-eq-nz-sums u t x e nz (no pt) (yes px) = ⊥-elim (pt (trans px (sym e)))
one-eq-nz-sums u t x e nz (no pt) (no px) =
  let lhs-eq = sums-cons-tail u (proj₁ t + proj₁ x , proj₂ t) [] pt
      rhs-eq = cong₂ _+_ (sums-cons-tail u x [] px)
                         (sums-cons-tail u t [] pt)
  in  trans lhs-eq
      (trans (sym (+-identityˡ (+ 0))) (sym rhs-eq))

-- 单元素 lt3：结果 = x ∷ (t ∷ [])
one-lt-sums : ∀ u t x → proj₂ t < proj₂ x →
  Dec (proj₂ u ≡ proj₂ t) → Dec (proj₂ u ≡ proj₂ x) →
  sums u (x ∷ (t ∷ [])) ≡ sums u (x ∷ []) + sums u (t ∷ [])
one-lt-sums u t x l (yes pt) (yes px) =
  ⊥-elim (<-irrefl refl
    (subst (λ z → proj₂ t < z) (trans (sym px) pt) l))
one-lt-sums u t x l (yes pt) (no px) =
  let lhs-eq = trans (sums-cons-tail u x (t ∷ []) px)
                     (sums-cons-head u t [] pt)
      rhs-eq = cong₂ _+_ (sums-cons-tail u x [] px)
                         (sums-cons-head u t [] pt)
  in  trans lhs-eq
      (trans (sym (+-identityˡ (proj₁ t + + 0))) (sym rhs-eq))
one-lt-sums u t x l (no pt) (yes px) =
  let lhs-eq = trans (sums-cons-head u x (t ∷ []) px)
                     (cong (λ w → proj₁ x + w) (sums-cons-tail u t [] pt))
      rhs-eq = cong₂ _+_ (sums-cons-head u x [] px)
                         (sums-cons-tail u t [] pt)
  in  trans lhs-eq
      (trans (sym (+-identityʳ (proj₁ x + + 0))) (sym rhs-eq))
one-lt-sums u t x l (no pt) (no px) =
  let lhs-eq = trans (sums-cons-tail u x (t ∷ []) px)
                     (sums-cons-tail u t [] pt)
      rhs-eq = cong₂ _+_ (sums-cons-tail u x [] px)
                         (sums-cons-tail u t [] pt)
  in  trans lhs-eq (trans (sym (+-identityˡ (+ 0))) (sym rhs-eq))

-- 双元素 gt3：结果 = t ∷ (x ∷ x₂ ∷ xs)
cons-gt-sums : ∀ u t x x₂ xs →
  Dec (proj₂ u ≡ proj₂ t) →
  sums u (t ∷ (x ∷ x₂ ∷ xs)) ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
cons-gt-sums u t x x₂ xs (yes pt) =
  trans (sums-cons-head u t (x ∷ x₂ ∷ xs) pt)
  (trans (solve 2 (λ S a → a :+ S := S :+ (a :+ con (+ 0))) refl
                 (sums u (x ∷ x₂ ∷ xs)) (proj₁ t))
         (sym (cong (λ w → sums u (x ∷ x₂ ∷ xs) + w)
                    (sums-cons-head u t [] pt))))
cons-gt-sums u t x x₂ xs (no pt) =
  trans (sums-cons-tail u t (x ∷ x₂ ∷ xs) pt)
  (trans (sym (+-identityʳ (sums u (x ∷ x₂ ∷ xs))))
         (sym (cong (λ w → sums u (x ∷ x₂ ∷ xs) + w)
                    (sums-cons-tail u t [] pt))))

-- 双元素 eq3-zero：结果 = x₂ ∷ xs（相消）
cons-eq-zero-sums : ∀ u t x x₂ xs →
  proj₂ t ≡ proj₂ x → proj₁ t + proj₁ x ≡ + 0 →
  Dec (proj₂ u ≡ proj₂ t) → Dec (proj₂ u ≡ proj₂ x) →
  sums u (x₂ ∷ xs) ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
cons-eq-zero-sums u t x x₂ xs e z (yes pt) (yes px) =
  let S = sums u (x₂ ∷ xs)
      rhs-eq = cong₂ _+_ (sums-cons-head u x (x₂ ∷ xs) px)
                         (sums-cons-head u t [] pt)
      z' : proj₁ x + (proj₁ t + + 0) ≡ + 0
      z' = trans (cong (λ w → proj₁ x + w) (+-identityʳ (proj₁ t)))
                 (trans (+-comm (proj₁ x) (proj₁ t)) z)
  in  trans (zero-shuffle S (proj₁ x) (proj₁ t + + 0) z') (sym rhs-eq)
cons-eq-zero-sums u t x x₂ xs e z (yes pt) (no px) = ⊥-elim (px (trans pt e))
cons-eq-zero-sums u t x x₂ xs e z (no pt) (yes px) = ⊥-elim (pt (trans px (sym e)))
cons-eq-zero-sums u t x x₂ xs e z (no pt) (no px) =
  let rhs-eq = cong₂ _+_ (sums-cons-tail u x (x₂ ∷ xs) px)
                         (sums-cons-tail u t [] pt)
  in  trans refl
      (trans (sym (+-identityʳ (sums u (x₂ ∷ xs)))) (sym rhs-eq))

-- 双元素 eq3-nz：结果 = m ∷ (x₂ ∷ xs)（m = 合并项）
cons-eq-nz-sums : ∀ u t x x₂ xs →
  proj₂ t ≡ proj₂ x → ¬ (proj₁ t + proj₁ x ≡ + 0) →
  Dec (proj₂ u ≡ proj₂ t) → Dec (proj₂ u ≡ proj₂ x) →
  sums u ((proj₁ t + proj₁ x , proj₂ t) ∷ (x₂ ∷ xs))
  ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
cons-eq-nz-sums u t x x₂ xs e nz (yes pt) (yes px) =
  trans (sums-cons-head u (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) pt)
  (trans (solve 3 (λ S a b → (a :+ b) :+ S := (b :+ S) :+ (a :+ con (+ 0))) refl
                 (sums u (x₂ ∷ xs)) (proj₁ t) (proj₁ x))
         (sym (cong₂ _+_ (sums-cons-head u x (x₂ ∷ xs) px)
                         (sums-cons-head u t [] pt))))
cons-eq-nz-sums u t x x₂ xs e nz (yes pt) (no px) = ⊥-elim (px (trans pt e))
cons-eq-nz-sums u t x x₂ xs e nz (no pt) (yes px) = ⊥-elim (pt (trans px (sym e)))
cons-eq-nz-sums u t x x₂ xs e nz (no pt) (no px) =
  trans (sums-cons-tail u (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) pt)
  (trans (sym (+-identityʳ (sums u (x₂ ∷ xs))))
         (sym (cong₂ _+_ (sums-cons-tail u x (x₂ ∷ xs) px)
                         (sums-cons-tail u t [] pt))))

-- 双元素 lt3：结果 = x ∷ (insertCᵌ t (x₂ ∷ xs) s)（递归）
cons-lt3-sums : ∀ u t x x₂ xs (p : proj₂ x₂ < proj₂ x) (l : proj₂ t < proj₂ x)
  (s : Canon (x₂ ∷ xs)) →
  Dec (proj₂ u ≡ proj₂ x) →
  (inner : SpecT t (x₂ ∷ xs)) →
  sums u (proj₁ inner) ≡ sums u (x₂ ∷ xs) + sums u (t ∷ []) →
  sums u (proj₁ (lt3-cons t x x₂ xs p l s inner)) ≡ sums u (x ∷ x₂ ∷ xs) + sums u (t ∷ [])
cons-lt3-sums u t x x₂ xs p l s (yes px) (w' , cw' , inj₁ btail) ih =
  trans (sums-cons-head u x w' px)
  (trans (cong (λ w → proj₁ x + w) ih)
         (trans (solve 3 (λ S a b → b :+ (S :+ a) := (b :+ S) :+ a) refl
                        (sums u (x₂ ∷ xs)) (sums u (t ∷ [])) (proj₁ x))
                (cong (λ w → w + sums u (t ∷ []))
                      (sym (sums-cons-head u x (x₂ ∷ xs) px)))))
cons-lt3-sums u t x x₂ xs p l s (yes px) (w' , cw' , inj₂ (h , r , eq , src)) ih =
  trans (sums-cons-head u x (h ∷ r) px)
  (trans (cong (λ w → proj₁ x + w) (trans (cong (λ v → sums u v) (sym eq)) ih))
         (trans (solve 3 (λ S a b → b :+ (S :+ a) := (b :+ S) :+ a) refl
                        (sums u (x₂ ∷ xs)) (sums u (t ∷ [])) (proj₁ x))
                (cong (λ w → w + sums u (t ∷ []))
                      (sym (sums-cons-head u x (x₂ ∷ xs) px)))))
cons-lt3-sums u t x x₂ xs p l s (no px) (w' , cw' , inj₁ btail) ih =
  trans (sums-cons-tail u x w' px)
  (trans ih
         (sym (cong (λ w → w + sums u (t ∷ []))
                    (sums-cons-tail u x (x₂ ∷ xs) px))))
cons-lt3-sums u t x x₂ xs p l s (no px) (w' , cw' , inj₂ (h , r , eq , src)) ih =
  trans (sums-cons-tail u x (h ∷ r) px)
  (trans (trans (cong (λ v → sums u v) (sym eq)) ih)
         (sym (cong (λ w → w + sums u (t ∷ []))
                    (sums-cons-tail u x (x₂ ∷ xs) px))))

-- ────────────────────────────────────────────────────────────────────
-- 核心引理：插入保持逐指数和（对 Canon 结构归纳）
-- ────────────────────────────────────────────────────────────────────

-- 双元素分支（with cmp3 精炼 insertCᵌ，辅助函数闭合算术）
insertCᵌ-sums : ∀ (u t : LaurentTerm) ts (c : Canon ts) →
  sums u (proj₁ (insertCᵌ t ts c)) ≡ sums u ts + sums u (t ∷ [])
insertCᵌ-sums u t [] c =
  sym (+-identityˡ (sums u (t ∷ [])))
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g = one-gt-sums u t x g (proj₂ u ≟ proj₂ t) (proj₂ u ≟ proj₂ x)
... | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes z = one-eq-zero-sums u t x e z (proj₂ u ≟ proj₂ t) (proj₂ u ≟ proj₂ x)
...   | no nz = one-eq-nz-sums u t x e nz (proj₂ u ≟ proj₂ t) (proj₂ u ≟ proj₂ x)
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  | lt3 _ _ l = one-lt-sums u t x l (proj₂ u ≟ proj₂ t) (proj₂ u ≟ proj₂ x)
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ g = cons-gt-sums u t x x₂ xs (proj₂ u ≟ proj₂ t)
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes z = cons-eq-zero-sums u t x x₂ xs e z
                 (proj₂ u ≟ proj₂ t) (proj₂ u ≟ proj₂ x)
...   | no nz = cons-eq-nz-sums u t x x₂ xs e nz
                 (proj₂ u ≟ proj₂ t) (proj₂ u ≟ proj₂ x)
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | lt3 _ _ l =
  cons-lt3-sums u t x x₂ xs p l s (proj₂ u ≟ proj₂ x)
    (insertCᵌ t (x₂ ∷ xs) s) (insertCᵌ-sums u t (x₂ ∷ xs) s)

-- ────────────────────────────────────────────────────────────────────
-- norm：fold insertCᵌ 产生规范形（路线 B）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- NoZero：无零系数谓词
-- ────────────────────────────────────────────────────────────────────

NoZero : Laurent → Set
NoZero [] = ⊤
NoZero ((c , n) ∷ ts) = (c ≢ + 0) × NoZero ts

-- sums 在「所有项指数 < proj₂ u」的列表上为零
sums-bound-zero : ∀ u xs → Canon xs →
  (∀ y → InT y xs → proj₂ y < proj₂ u) → sums u xs ≡ + 0
sums-bound-zero u [] _ _ = refl
sums-bound-zero u ((c , n) ∷ ys) cy bound with proj₂ u ≟ n
... | yes un = ⊥-elim (<-irrefl refl
  (subst (λ z → z < proj₂ u) (sym un) (bound (c , n) (here (c , n) ys))))
... | no _ = sums-bound-zero u ys (canon-tail cy)
  (λ y iy → bound y (there y (c , n) ys iy))

-- normC：递归构造规范形 + Canon 证据
normC : (ts : Laurent) → Σ Laurent (λ w → Canon w)
normC [] = ([] , canon-nil)
normC (t ∷ ts) with normC ts
... | (w , cw) with insertCᵌ t w cw
...   | (w' , cw' , _) = (w' , cw')

-- norm：提取规范形
norm : Laurent → Laurent
norm ts = proj₁ (normC ts)

-- cmp3-gt3-lemma：n' < n 时 cmp3 返回 gt3（对 cmp3 结果模式匹配）
cmp3-gt3-lemma : ∀ n n' → (p : n' < n) → Σ (n' < n) (λ p' → cmp3 n n' ≡ gt3 n n' p')
cmp3-gt3-lemma n n' p with cmp3 n n'
... | gt3 .n .n' p' = (p' , refl)
... | lt3 .n .n' q = ⊥-elim (<-irrefl refl (<-trans p q))
... | eq3 .n .n' e = ⊥-elim (<-irrefl refl (subst (λ z → z < n) (sym e) p))

-- canon-sums-unique（sums 相等 → Canon 相等）待下轮实现。
-- ────────────────────────────────────────────────────────────────────
-- ℤ 消去律
-- ────────────────────────────────────────────────────────────────────

+-cancelˡ : ∀ a b c → a + b ≡ a + c → b ≡ c
+-cancelˡ a b c eq =
  trans (sym (+-identityˡ b))
  (trans (cong (λ w → w + b) (sym (+-inverseˡ a)))
  (trans (+-assoc (- a) a b)
  (trans (cong (λ w → (- a) + w) eq)
  (trans (sym (+-assoc (- a) a c))
  (trans (cong (λ w → w + c) (+-inverseˡ a))
         (+-identityˡ c))))))

-- ────────────────────────────────────────────────────────────────────
-- ℤ 右消去律
-- ────────────────────────────────────────────────────────────────────

+-cancelʳ : ∀ a b c → b + a ≡ c + a → b ≡ c
+-cancelʳ a b c eq = +-cancelˡ a b c (trans (sym (+-comm b a)) (trans eq (+-comm c a)))

-- ────────────────────────────────────────────────────────────────────
-- hexp-lemma：从 sums 等式推出系数等式
-- ────────────────────────────────────────────────────────────────────

hexp-lemma : ∀ (u : LaurentTerm) (c₁ n₁ c₂ n₂ : ℤ) (xs ys : Laurent) →
  n₁ ≡ n₂ →
  proj₂ u ≡ n₁ →
  sums u ((c₁ , n₁) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ ys) →
  (∀ v → sums v xs ≡ sums v ys) →
  c₁ + sums u xs ≡ c₂ + sums u ys
hexp-lemma u c₁ n₁ c₂ n₂ xs ys e ue h hxs =
  trans (sym (sums-cons-head u (c₁ , n₁) xs ue))
  (trans h
         (sums-cons-head u (c₂ , n₂) ys (trans ue e)))

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- 直接用 sums-cons-head 展开 + +-cancelʳ 消去，不走 hexp-lemma
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- 用 subst 沿 sums-cons-head 重写（case_of_ 化后展开定义性成立）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- 用 subst 沿 sums-cons-head 重写（case_of_ 化后展开定义性成立）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- 用 case_of_ 分支 + sums-bound-zero 直推（避开 h 展开）
-- ────────────────────────────────────────────────────────────────────

-- ────────────────────────────────────────────────────────────────────
-- canon-sums-unique：sums 相等 → Canon 相等（枢纽引理）
-- 关键：with n₁ ≟ n₁ 抽象所有语法出现（包括 h 类型内部），强制 sums 归约
-- ────────────────────────────────────────────────────────────────────

-- canon-sums-unique 待下轮：with n₁ ≟ n₁ 无法抽象 h 类型内部
-- （h : ∀ u → sums u ((c₁ , n₁) ∷ xs) ≡ ...，u 是绑定变量，
--  with 无法抽象绑定器内部的 n₁ ≟ n₁ 语法出现）。
-- h'（case_of_ + sums-bound-zero）只能证 sums xs ≡ sums ys（两者都为 0），
-- 无法推出 c₁ ≡ c₂——必须用 h (c₁ , n₁) + sums-cons-head 展开 main。
-- 唯一出路：改 sums 定义（用 with 而非 case_of_），让 sums-cons-head
-- 的 with 与 sums 的 with 共精炼——但这会破坏 sums 的定义性展开。
-- norm-+ 依赖此引理 + norm-idem + insertCᵌ-sums（已证）。

-- ────────────────────────────────────────────────────────────────────
-- ── 2026-10-11 补件（Laurent.norm-plus / ring-axioms 前置件）──
--   路线：norm 保 sums（不保置换——insertCᵌ 会合并同指数项），
--   故一切等式走「sums 逐点相等 → canon 唯一性提升」。
--   零系事实：insertCᵌ 的 cancel 分支移除零系对（BTail.bt-eq₂ : w ≡ bt-xs'），
--   合并分支只存非零和 ⇒ NoZero 输入经 norm 保持（norm-nozero 见后续）。
-- ────────────────────────────────────────────────────────────────────

open import Data.Integer.Properties using (+-identityʳ; +-comm)
open import Relation.Binary.PropositionalEquality using (trans; cong; sym)

-- 尾展开：t∷ts 的 sums = 单点 ts 与余尾之和
sums-uncons : ∀ (u t : LaurentTerm) ts →
  sums u (t ∷ ts) ≡ sums u (t ∷ []) + sums u ts
sums-uncons u (c , n) ts with proj₂ u ≟ n
... | yes _ = cong (_+ sums u ts) (sym (+-identityʳ c))
... | no  _ = sym (+-identityˡ (sums u ts))

-- normC 保 sums（工作马）：对 ts 归纳，插入件 insertCᵌ-sums 收口
normC-s : ∀ (u : LaurentTerm) (ts : Laurent) →
  sums u (proj₁ (normC ts)) ≡ sums u ts
normC-s u [] = refl
normC-s u (t ∷ ts) with normC ts in eq
... | (w , cw) with insertCᵌ t w cw in eq2
... | (w' , _ , _) = trans (sym (cong (λ z → sums u (proj₁ z)) eq2)) (trans head-step tail-step)
  where
    -- IH 沿 with 等式搬运：proj₁ (normC ts) ≡ w
    subst-w : normC ts ≡ (w , cw) → sums u w ≡ sums u ts
    subst-w e = trans (sym (cong (λ z → sums u (proj₁ z)) e)) (normC-s u ts)
    -- 插入件收口：[插入结果] = 旧 sums + 单点 t
    head-step : sums u (proj₁ (insertCᵌ t w cw)) ≡ sums u ts + sums u (t ∷ [])
    head-step = trans (insertCᵌ-sums u t w cw) (cong (_+ sums u (t ∷ [])) (subst-w eq))
    -- 和序换位 + 尾展开对齐
    tail-step : sums u ts + sums u (t ∷ []) ≡ sums u (t ∷ ts)
    tail-step = trans (+-comm (sums u ts) (sums u (t ∷ []))) (sym (sums-uncons u t ts))

-- 规范形保 sums（对外）
norm-sums : ∀ (u : LaurentTerm) (xs : Laurent) →
  sums u (norm xs) ≡ sums u xs
norm-sums = normC-s



-- ────────────────────────────────────────────────────────────────────
-- ── 2026-10-11 Stage3 ──
-- 四难律收口·核心件：NoZero 保持 / canon-sums-unique-nz / sums 拆合
--   路线：sums 逐点相等 → canon-sums-unique-nz 提升（NoZero 前提）。
--   为何要 NoZero：insertCᵌ 保留孤零项（insert (0,n) [] = [(0,n)]），
--   含零项的 Canon 之间 sums 相等推不出列表相等（反例 [(0,n)] vs []）。
-- ────────────────────────────────────────────────────────────────────

open import Data.Integer.Properties using (+-assoc; +-identityˡ)
open import Sovereign.Algebra.LaurentCanon using (canon-unique; ∈[]-absurd)
open import Sovereign.Algebra.LaurentBase using (_++L_)

-- NoZero 结构件
noz-head : ∀ (c : ℤ) n ts → NoZero ((c , n) ∷ ts) → c ≢ + 0
noz-head c n ts nz = proj₁ nz

noz-tail : ∀ (c : ℤ) n ts → NoZero ((c , n) ∷ ts) → NoZero ts
noz-tail c n ts nz = proj₂ nz

-- InT 成员的系数非零（成员构造子即字面相等）
inT-noz : ∀ (t : LaurentTerm) ts → NoZero ts → InT t ts → proj₁ t ≢ + 0
inT-noz (c , n) ((.c , .n) ∷ ts) (hn , _) (here _ _) = hn
inT-noz (c , n) (u ∷ ts) (_ , nt) (there _ _ _ w) = inT-noz (c , n) ts nt w

-- ++L 保 NoZero（拼接不造零系数项）
++L-nozero : ∀ xs ys → NoZero xs → NoZero ys → NoZero (xs ++L ys)
++L-nozero [] ys _ ny = ny
++L-nozero ((c , n) ∷ xs) ys (hc , nx) ny = hc , ++L-nozero xs ys nx ny

-- 严格序即相异
<-≢ : ∀ {a b : ℤ} → a < b → a ≢ b
<-≢ lt refl = <-irrefl refl lt

-- sums 只依赖 u 的指数
sums-idx : ∀ u v ts → proj₂ u ≡ proj₂ v → sums u ts ≡ sums v ts
sums-idx u v [] _ = refl
sums-idx u v ((c , n) ∷ ts) e with proj₂ u ≟ n | proj₂ v ≟ n
... | yes _ | yes _ = cong (λ z → c + z) (sums-idx u v ts e)
... | yes p | no q = ⊥-elim (q (trans (sym e) p))
... | no p | yes q = ⊥-elim (p (trans e q))
... | no _ | no _ = sums-idx u v ts e

-- 头指数相异 ⇒ sums 跳过头
sums-skip-≠ : ∀ u (x : LaurentTerm) xs → proj₂ u ≢ proj₂ x → sums u (x ∷ xs) ≡ sums u xs
sums-skip-≠ u (c , n) xs ne with proj₂ u ≟ n
... | yes p = ⊥-elim (ne p)
... | no _ = refl

-- 全员指数 ≠ proj₂ u ⇒ sums 为零
sums-absent : ∀ u xs → Canon xs → (∀ y → InT y xs → proj₂ y ≢ proj₂ u) → sums u xs ≡ + 0
sums-absent u [] _ _ = refl
sums-absent u ((c , n) ∷ ys) cy ne with proj₂ u ≟ n
... | yes p = ⊥-elim (ne (c , n) (here (c , n) ys) (sym p))
... | no _ = sums-absent u ys (canon-tail cy) (λ y iy → ne y (there y (c , n) ys iy))

-- Canon 成员提取：sums t xs = proj₁ t（同指数唯一）
sums-member : ∀ t xs → Canon xs → InT t xs → sums t xs ≡ proj₁ t
sums-member (c , n) ((.c , .n) ∷ []) (canon-one _) (here _ _) with n ≟ n
... | yes _ = +-identityʳ c
... | no q = ⊥-elim (q refl)
sums-member (c , n) ((.c , .n) ∷ (y ∷ ys)) (canon-cons _ y ys p s) (here _ _) with n ≟ n
... | yes _ = trans (cong (λ z → c + z) (sums-absent (c , n) (y ∷ ys) s below)) (+-identityʳ c)
  where
  below : ∀ h → InT h (y ∷ ys) → proj₂ h ≢ proj₂ (c , n)
  below .y (here .y .ys) = <-≢ p
  below h (there .h .y .ys iy) = <-≢ (<-trans (canon-<-head s h iy) p)
... | no q = ⊥-elim (q refl)
sums-member (c , n) ((c' , n') ∷ ts) cx (there _ _ _ w) =
  trans (sums-skip-≠ (c , n) (c' , n') ts (<-≢ (canon-<-head cx (c , n) w)))
        (sums-member (c , n) ts (canon-tail cx) w)

-- 指数分裂：ys 中存在同指数项，或全员指数相异（Canon 下 decidable）
exp-split : ∀ (t : LaurentTerm) (xs : Laurent) → Canon xs →
  (Σ LaurentTerm (λ y → InT y xs × (proj₂ y ≡ proj₂ t)))
  ⊎ (∀ y → InT y xs → proj₂ y ≢ proj₂ t)
exp-split t [] _ = inj₂ (λ y iy → ⊥-elim (∈[]-absurd iy))
exp-split t (x ∷ xs) cx with proj₂ t ≟ proj₂ x
... | yes e = inj₁ (x , here x xs , sym e)
... | no ne with exp-split t xs (canon-tail cx)
...   | inj₁ (y , iy , ey) = inj₁ (y , there y x xs iy , ey)
...   | inj₂ f = inj₂ (g ne f)
  where
  g : proj₂ t ≢ proj₂ x → (∀ y → InT y xs → proj₂ y ≢ proj₂ t) →
      ∀ y → InT y (x ∷ xs) → proj₂ y ≢ proj₂ t
  g ne f .x (here .x .xs) = λ e → ne (sym e)
  g ne f y (there .y .x .xs iy) = f y iy

-- 成员沿 sums 相等迁移（NoZero 下）
inT-resp-sums : ∀ xs ys → Canon xs → Canon ys → NoZero xs → NoZero ys →
  (∀ u → sums u xs ≡ sums u ys) → ∀ t → InT t xs → InT t ys
inT-resp-sums xs ys cx cy nx ny eqs t itx with exp-split t ys cy
... | inj₂ absent = ⊥-elim (ct≢0 ct≡0)
  where
  ct≢0 : proj₁ t ≢ + 0
  ct≢0 = inT-noz t xs nx itx
  ct≡0 : proj₁ t ≡ + 0
  ct≡0 = trans (sym (sums-member t xs cx itx)) (trans (eqs t) (sums-absent t ys cy absent))
... | inj₁ (y , iy , ey) = subst (λ z → InT z ys) y≡t iy
  where
  coef-≡ : proj₁ y ≡ proj₁ t
  coef-≡ = trans (sym (sums-member y ys cy iy))
                (trans (sums-idx y t ys ey) (trans (sym (eqs t)) (sums-member t xs cx itx)))
  y≡t : y ≡ t
  y≡t = cong₂ _,_ coef-≡ ey

-- 枢纽：Canon + NoZero 下 sums 逐点相等 ⇒ 列表相等
canon-sums-unique-nz : ∀ xs ys → Canon xs → Canon ys → NoZero xs → NoZero ys →
  (∀ u → sums u xs ≡ sums u ys) → xs ≡ ys
canon-sums-unique-nz xs ys cx cy nx ny eqs =
  canon-unique xs ys cx cy
    (inT-resp-sums xs ys cx cy nx ny eqs)
    (inT-resp-sums ys xs cy cx ny nx (λ u → sym (eqs u)))

-- sums 拆合律
sums-++L : ∀ u xs ys → sums u (xs ++L ys) ≡ sums u xs + sums u ys
sums-++L u [] ys = sym (+-identityˡ (sums u ys))
sums-++L u ((c , n) ∷ xs) ys with proj₂ u ≟ n
... | yes _ = trans (cong (λ z → c + z) (sums-++L u xs ys)) (sym (+-assoc c (sums u xs) (sums u ys)))
... | no _ = sums-++L u xs ys


-- insertCᵌ 保 NoZero（镜像 insertCᵌ 分支；合并项存非零和、消去项整项移除）
--   lt3 递归分支按 insertCᵌ-sums 的「spec 作参数」习语（cons-lt3-noz），无 with-in 运输
one-eqz-noz : ∀ (t x : LaurentTerm) → NoZero [] 
one-eqz-noz t x = tt

one-eqnz-noz : ∀ (t x : LaurentTerm) → ((proj₁ t + proj₁ x) ≢ + 0) → NoZero (((proj₁ t + proj₁ x) , proj₂ t) ∷ [])
one-eqnz-noz t x z = z , tt

cons-eqz-noz : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) → NoZero (x₂ ∷ xs) → NoZero (x₂ ∷ xs)
cons-eqz-noz t x x₂ xs nz = nz

cons-eqnz-noz : ∀ (t x x₂ : LaurentTerm) (xs : Laurent) → ((proj₁ t + proj₁ x) ≢ + 0) →
  NoZero (x₂ ∷ xs) → NoZero (((proj₁ t + proj₁ x) , proj₂ t) ∷ (x₂ ∷ xs))
cons-eqnz-noz t x x₂ xs z nz = z , nz

cons-lt3-noz : ∀ (t x x₂ : LaurentTerm) (xs : Laurent)
               (p : proj₂ x₂ < proj₂ x) (l : proj₂ t < proj₂ x) (s : Canon (x₂ ∷ xs))
               (sp : SpecT t (x₂ ∷ xs)) → NoZero (proj₁ sp) → (proj₁ x ≢ + 0) →
               NoZero (proj₁ (lt3-cons t x x₂ xs p l s sp))
cons-lt3-noz t x x₂ xs p l s (w' , _ , inj₁ _) nzw hx = hx , nzw
cons-lt3-noz t x x₂ xs p l s (w' , _ , inj₂ (h , r , eq , _)) nzw hx =
  hx , subst NoZero eq nzw

insertCᵌ-nozero : ∀ (t : LaurentTerm) ts (c : Canon ts) →
  NoZero (t ∷ ts) → NoZero (proj₁ (insertCᵌ t ts c))
insertCᵌ-nozero t [] c nt = nt
insertCᵌ-nozero t (x ∷ []) (canon-one .x) (nt , nx) with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ _ = nt , nx
... | eq3 _ _ _ with (proj₁ t + proj₁ x) ≟ + 0
...   | yes _ = one-eqz-noz t x
...   | no z = one-eqnz-noz t x z
insertCᵌ-nozero t (x ∷ []) (canon-one .x) (nt , nx) | lt3 _ _ _ = proj₁ nx , nt , tt
insertCᵌ-nozero t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s) (nt , hx , hrest)
  with cmp3 (proj₂ t) (proj₂ x)
... | gt3 _ _ _ = nt , hx , hrest
... | eq3 _ _ _ with (proj₁ t + proj₁ x) ≟ + 0
...   | yes _ = cons-eqz-noz t x x₂ xs hrest
...   | no z = cons-eqnz-noz t x x₂ xs z hrest
insertCᵌ-nozero t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s) (nt , hx , hrest)
  | lt3 _ _ l =
  cons-lt3-noz t x x₂ xs p l s (insertCᵌ t (x₂ ∷ xs) s)
    (insertCᵌ-nozero t (x₂ ∷ xs) s (nt , hrest)) hx

-- norm 保 NoZero（对 ts 归纳：插入件 insertCᵌ-nozero 收口）
norm-nozero : ∀ ts → NoZero ts → NoZero (norm ts)
norm-nozero [] _ = tt
norm-nozero (t ∷ ts) nt with normC ts in eq
... | (w , cw) with insertCᵌ t w cw in eq2
... | (w' , _ , _) = subst NoZero (cong proj₁ eq2)
    (insertCᵌ-nozero t w cw
      (proj₁ nt , subst NoZero (cong proj₁ eq) (norm-nozero ts (proj₂ nt))))

-- ────────────────────────────────────────────────────────────────────
-- ── 2026-10-11 Stage3（续）── sums 与置换/cons 相容
open import Data.List.Relation.Binary.Permutation.Propositional
  using (_↭_; prep; swap) renaming (refl to ↭-refl; trans to ↭-trans)
-- ────────────────────────────────────────────────────────────────────

-- cons 同步（头决策同一，尾 IH）
sums-cons-cong : ∀ u (x : LaurentTerm) {xs ys} → sums u xs ≡ sums u ys →
                 sums u (x ∷ xs) ≡ sums u (x ∷ ys)
sums-cons-cong u (c , n) {xs} {ys} ih with proj₂ u ≟ n
... | yes _ = cong (λ z → c + z) ih
... | no _ = ih


-- 单层剥离（证据版——每引理自带一层决策，goal 零抽象）
sums-head-yes : ∀ u (x : LaurentTerm) xs → proj₂ u ≡ proj₂ x → sums u (x ∷ xs) ≡ proj₁ x + sums u xs
sums-head-yes u (c , n) xs p with proj₂ u ≟ n
... | yes _ = refl
... | no q = ⊥-elim (q p)

sums-head-no : ∀ u (x : LaurentTerm) xs → proj₂ u ≢ proj₂ x → sums u (x ∷ xs) ≡ sums u xs
sums-head-no u (c , n) xs q with proj₂ u ≟ n
... | yes p = ⊥-elim (q p)
... | no _ = refl

-- 双头交换（dispatch 按 Dec 参数模式匹配——goal 零归约零抽象；
--   四案具名拆分：各案 = 前剥 sums-head-* 等式拼接 → ℤ 交换代数，每链 ≤3）
sums-swap2-yy : ∀ u (c₁ : ℤ) n₁ c₂ n₂ xs →
  proj₂ u ≡ n₁ → proj₂ u ≡ n₂ →
  sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
sums-swap2-yy u c₁ n₁ c₂ n₂ xs p₁ p₂ = trans yy-1 (trans yy-2 yy-3)
  where
  yy-1 : sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ (c₁ + c₂) + sums u xs
  yy-1 = trans (sums-head-yes u (c₁ , n₁) ((c₂ , n₂) ∷ xs) p₁)
           (trans (cong (λ z → c₁ + z) (sums-head-yes u (c₂ , n₂) xs p₂))
                  (sym (+-assoc c₁ c₂ (sums u xs))))
  yy-2 : (c₁ + c₂) + sums u xs ≡ c₂ + sums u ((c₁ , n₁) ∷ xs)
  yy-2 = trans (cong (λ z → z + sums u xs) (+-comm c₁ c₂))
           (trans (+-assoc c₂ c₁ (sums u xs))
                  (cong (λ z → c₂ + z) (sym (sums-head-yes u (c₁ , n₁) xs p₁))))
  yy-3 : c₂ + sums u ((c₁ , n₁) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
  yy-3 = sym (sums-head-yes u (c₂ , n₂) ((c₁ , n₁) ∷ xs) p₂)

sums-swap2-yn : ∀ u (c₁ : ℤ) n₁ c₂ n₂ xs →
  proj₂ u ≡ n₁ → proj₂ u ≢ n₂ →
  sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
sums-swap2-yn u c₁ n₁ c₂ n₂ xs p₁ q₂ = trans yn-1 yn-2
  where
  yn-1 : sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ c₁ + sums u xs
  yn-1 = trans (sums-head-yes u (c₁ , n₁) ((c₂ , n₂) ∷ xs) p₁)
           (cong (λ z → c₁ + z) (sums-head-no u (c₂ , n₂) xs q₂))
  yn-2 : c₁ + sums u xs ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
  yn-2 = trans (sym (sums-head-yes u (c₁ , n₁) xs p₁))
           (sym (sums-head-no u (c₂ , n₂) ((c₁ , n₁) ∷ xs) q₂))

sums-swap2-ny : ∀ u (c₁ : ℤ) n₁ c₂ n₂ xs →
  proj₂ u ≢ n₁ → proj₂ u ≡ n₂ →
  sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
sums-swap2-ny u c₁ n₁ c₂ n₂ xs q₁ p₂ = trans ny-1 ny-2
  where
  ny-1 : sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ c₂ + sums u xs
  ny-1 = trans (sums-head-no u (c₁ , n₁) ((c₂ , n₂) ∷ xs) q₁)
           (sums-head-yes u (c₂ , n₂) xs p₂)
  ny-2 : c₂ + sums u xs ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
  ny-2 = sym (trans (sums-head-yes u (c₂ , n₂) ((c₁ , n₁) ∷ xs) p₂)
               (cong (λ z → c₂ + z) (sums-head-no u (c₁ , n₁) xs q₁)))

sums-swap2-nn : ∀ u (c₁ : ℤ) n₁ c₂ n₂ xs →
  proj₂ u ≢ n₁ → proj₂ u ≢ n₂ →
  sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
sums-swap2-nn u c₁ n₁ c₂ n₂ xs q₁ q₂ = trans nn-1 nn-2
  where
  nn-1 : sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ sums u xs
  nn-1 = trans (sums-head-no u (c₁ , n₁) ((c₂ , n₂) ∷ xs) q₁)
           (sums-head-no u (c₂ , n₂) xs q₂)
  nn-2 : sums u xs ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
  nn-2 = sym (trans (sums-head-no u (c₂ , n₂) ((c₁ , n₁) ∷ xs) q₂)
               (sums-head-no u (c₁ , n₁) xs q₁))

sums-swap2 : ∀ u (x y : LaurentTerm) xs → sums u (x ∷ y ∷ xs) ≡ sums u (y ∷ x ∷ xs)
sums-swap2 u (c₁ , n₁) (c₂ , n₂) xs = dispatch (proj₂ u ≟ n₁) (proj₂ u ≟ n₂)
  where
  dispatch : (d₁ : Dec (proj₂ u ≡ n₁)) (d₂ : Dec (proj₂ u ≡ n₂)) →
             sums u ((c₁ , n₁) ∷ (c₂ , n₂) ∷ xs) ≡ sums u ((c₂ , n₂) ∷ (c₁ , n₁) ∷ xs)
  dispatch (yes p₁) (yes p₂) = sums-swap2-yy u c₁ n₁ c₂ n₂ xs p₁ p₂
  dispatch (yes p₁) (no q₂) = sums-swap2-yn u c₁ n₁ c₂ n₂ xs p₁ q₂
  dispatch (no q₁) (yes p₂) = sums-swap2-ny u c₁ n₁ c₂ n₂ xs q₁ p₂
  dispatch (no q₁) (no q₂) = sums-swap2-nn u c₁ n₁ c₂ n₂ xs q₁ q₂

-- sums 对置换不变（refl/prep/swap/trans 四构造子）
sums-resp-↭ : ∀ u {xs ys} → xs ↭ ys → sums u xs ≡ sums u ys
sums-resp-↭ u ↭-refl = refl
sums-resp-↭ u (prep x p) = sums-cons-cong u x (sums-resp-↭ u p)
sums-resp-↭ u (swap x y p) =
  trans (sums-swap2 u x y _)
    (sums-cons-cong u y (sums-cons-cong u x (sums-resp-↭ u p)))
sums-resp-↭ u (↭-trans p q) = trans (sums-resp-↭ u p) (sums-resp-↭ u q)
