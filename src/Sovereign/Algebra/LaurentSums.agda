{-# OPTIONS --rewriting --guardedness #-}

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
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; canon-nil; canon-one; canon-cons;
         canon-tail; canon-<-head; InT; here; there)
open import Sovereign.Algebra.LaurentNorm
  using (insertCᵌ; Cmp3; cmp3; lt3; eq3; gt3; BTail; SpecT; lt3-cons)

-- ────────────────────────────────────────────────────────────────────
-- sums：逐指数系数和
-- ────────────────────────────────────────────────────────────────────

sums : LaurentTerm → Laurent → ℤ
sums u [] = + 0
sums u ((c , n) ∷ ts) with proj₂ u ≟ n
... | yes _ = c + sums u ts
... | no _  = sums u ts

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

-- normC-idem：Canon 上 normC 幂等（待下轮）
-- 需要 cmp3-gt3-lemma（已证）+ insertCᵌ 的 gt3 分支展开。
-- norm-idem / canon-sums-unique / norm-+ 依赖此引理。
