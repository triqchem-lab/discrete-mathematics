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
-- 设计要点：
--   ① 插入项贡献统一写成 sums u (t ∷ []) 而非独立 δ 函数
--      （δ 与 sums 双函数的 with-aux 互不精炼——本会话实测）；
--   ② 算术分支用 stdlib ℤ-ring solver（Data.Integer.Solver）：
--      with 精炼后各目标归约为纯 ℤ 线性式，solver 一步闭合。
--
-- ℤ 算术复用 stdlib（+-assoc/+-comm/+-identityˡ/+-identityʳ）。
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
-- 各分支的算术由 ℤ-ring solver 闭合
-- ────────────────────────────────────────────────────────────────────

-- 零和：dx + dt ≡ + 0 ⟹ S ≡ (dx + S) + dt
-- S + (c_t + c_x) ≡ (c_x + S) + c_t
sums-shuffle : ∀ S c_x c_t →
  S + (c_t + c_x) ≡ (c_x + S) + c_t
sums-shuffle S c_x c_t =
  trans (sym (trans (cong (λ w → w + S) (+-comm c_x c_t))
                    (+-comm (c_t + c_x) S)))
  (trans (+-assoc c_x c_t S)
  (trans (cong (λ w → c_x + w) (+-comm c_t S))
         (sym (+-assoc c_x S c_t))))

zero-shuffle : ∀ S dx dt → dx + dt ≡ + 0 → S ≡ (dx + S) + dt
zero-shuffle S dx dt z =
  sym (trans (+-assoc dx S dt)
  (trans (cong (λ w → dx + w) (+-comm S dt))
  (trans (sym (+-assoc dx dt S))
  (trans (cong (_+ S) z)
         (+-identityˡ S)))))

insertCᵌ-sums : ∀ (u t : LaurentTerm) ts (c : Canon ts) →
  sums u (proj₁ (insertCᵌ t ts c)) ≡ sums u ts + sums u (t ∷ [])
insertCᵌ-sums u t [] c =
  sym (+-identityˡ (sums u (t ∷ [])))

insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  with cmp3 (proj₂ t) (proj₂ x) | proj₂ u ≟ proj₂ t | proj₂ u ≟ proj₂ x
... | gt3 _ _ g | yes pt | yes px =
  ⊥-elim (<-irrefl refl
    (subst (λ z → z < proj₂ t) pt
      (subst (λ z → z < proj₂ t) (sym px) g)))
... | gt3 _ _ g | yes pt | no px = refl
... | gt3 _ _ g | no pt | yes px =
  solve 1 (λ a → a :+ con (+ 0) := (a :+ con (+ 0)) + con (+ 0)) refl (proj₁ x)
... | gt3 _ _ g | no pt | no px = refl
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  | eq3 _ _ e with (proj₁ t + proj₁ x) ≟ + 0
...   | yes z with proj₂ u ≟ proj₂ t | proj₂ u ≟ proj₂ x
...     | yes pt | yes px =
  trans (sym z)
  (trans (+-comm (proj₁ t) (proj₁ x))
         (sym (cong₂ _+_ (+-identityʳ (proj₁ x)) (+-identityʳ (proj₁ t)))))
...     | yes pt | no px =
  ⊥-elim (px (trans pt (sym e)))
...     | no pt | yes px =
  ⊥-elim (pt (trans (sym px) e))
...     | no pt | no px =
  sym (+-identityˡ (+ 0))
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  | eq3 _ _ e
  | no _ with proj₂ u ≟ proj₂ t | proj₂ u ≟ proj₂ x
...     | yes pt | no px = ⊥-elim (px (trans pt (sym e)))
...     | no pt | yes px = ⊥-elim (pt (trans (sym px) e))
...     | no pt | no px =
  trans (cong (λ w → (proj₁ t + proj₁ x) + w) (+-identityˡ (sums u [])))
        (sym (trans (+-assoc (proj₁ t) (proj₁ x) (sums u []))
                    (cong (λ w → proj₁ t + w) (+-identityʳ (sums u [])))))
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  | lt3 _ _ l with proj₂ u ≟ proj₂ t | proj₂ u ≟ proj₂ x
...     | yes pt | no px =
  trans (+-assoc (proj₁ x) (sums u (t ∷ [])) (sums u (t ∷ [])))
        (cong (λ w → (proj₁ x + w) + sums u (t ∷ []))
              (sym (+-identityʳ (sums u (t ∷ [])))))
...     | no pt | yes px =
  trans (sym (+-identityˡ (sums u (t ∷ []))))
        (sym (trans (+-assoc (+ 0) (sums u (t ∷ [])) (sums u (t ∷ [])))
                    (cong (λ w → + 0 + w) (sym (+-identityʳ (sums u (t ∷ [])))))))
...     | no pt | no px = refl
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  | lt3 _ _ l
  | yes pt | yes px =
  ⊥-elim (px (trans pt (sym l)))

-- cons 分支
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  with cmp3 (proj₂ t) (proj₂ x) | (proj₁ t + proj₁ x) ≟ + 0
     | proj₂ u ≟ proj₂ x | proj₂ u ≟ proj₂ t
... | gt3 _ _ g | _ | _ | yes pt =
  solve 2 (λ S a → a + S := S + (a :+ con (+ 0))) refl
         (sums u (x ∷ x₂ ∷ xs)) (proj₁ t)
... | gt3 _ _ g | _ | _ | no pt =
  solve 1 (λ S → S := S + con (+ 0)) refl (sums u (x ∷ x₂ ∷ xs))
... | eq3 _ _ e | yes z | _ | _ =
  refl
... | eq3 _ _ e | no nz | yes ux | yes pt =
  let z' : proj₂ x + (proj₂ t + + 0) ≡ + 0
      z' = trans (+-assoc (proj₂ x) (proj₂ t) (+ 0))
                 (trans (cong (λ w → (proj₂ x) + w) (+-comm (proj₂ t) (+ 0))) e-z)
  in  trans (insertCᵌ-sums u m (x₂ ∷ xs) s)
            (zero-shuffle (sums u (x₂ ∷ xs)) (proj₂ x) (proj₂ t + + 0) z')
    where
    m = (proj₁ t + proj₁ x , proj₂ t)
    e-z : proj₂ t + proj₂ x ≡ + 0
    e-z = trans (+-comm (proj₂ t) (proj₂ x)) e
... | eq3 _ _ e | no nz | yes ux | no pt =
  ⊥-elim (pt (trans (sym ux) e))
... | eq3 _ _ e | no nz | no ux | yes pt =
  ⊥-elim (ux (trans (sym pt) e))
... | eq3 _ _ e | no nz | no ux | no pt with insertCᵌ (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) s
...     | (w' , cw' , inj₁ btail) with BTail.bt-eq₂ btail
...       | beq₂ =
    trans (cong (λ v → sums u v) beq₂)
          (sym (+-identityʳ (sums u (x₂ ∷ xs))))
...     | (w' , cw' , inj₂ (h , r , eq , src)) =
    insertCᵌ-sums u (proj₁ t + proj₁ x , proj₂ t) (x₂ ∷ xs) s
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | lt3 _ _ l | _ | yes ux | _ with insertCᵌ t (x₂ ∷ xs) s
...   | (w' , cw' , dj') =
  trans (cong (λ w → proj₁ x + w) (insertCᵌ-sums u t (x₂ ∷ xs) s))
        (sym (+-assoc (proj₁ x) (sums u (x₂ ∷ xs)) (sums u (t ∷ []))))
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | lt3 _ _ l | _ | no ux | _ with insertCᵌ t (x₂ ∷ xs) s
...   | (w' , cw' , dj') =
  trans (insertCᵌ-sums u t (x₂ ∷ xs) s)
        (sym (trans (+-identityˡ (sums u (x₂ ∷ xs) + sums u (t ∷ [])))
                    (cong (λ w → w + sums u (t ∷ []))
                          (sym (+-identityˡ (sums u (x₂ ∷ xs)))))))
