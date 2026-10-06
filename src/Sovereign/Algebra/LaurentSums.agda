{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Algebra.LaurentSums
-- Laurent 项列表的逐指数系数和（sums）及其在规范化插入下的不变量。
--
-- 数学背景：sums u p = 项列表 p 中所有指数等于 exp u 的项的系数之和
-- （ℤ 加法）。规范化插入 insertCᵌ（LaurentNorm）的核心不变量：
--   sums u (insertCᵌ 结果) ≡ sums u ts + δ u t
-- 其中 δ u t = （exp u ≡ exp t ? 系数 t : 0）。
-- 该不变量 + canon-unique（LaurentCanon）⟹ 规范形交换律 norm (a ++ b) ≡
-- norm (b ++ a)（sums 可加性 sums-++），⟹ 规范形上的逐点分配律。
--
-- ℤ 算术全部复用 stdlib（+-assoc/+-comm/+-identityˡ/+-identityʳ）。
--
-- 0 postulate / 0 hole。
module Sovereign.Algebra.LaurentSums where

open import Data.Integer using (ℤ; _≤_; _<_; +_; _+_)
open import Data.Integer.Properties
  using (_≟_; _<?_; _≤?_; ≤-antisym; <-trans; <-irrefl; ≰⇒>;
         +-assoc; +-comm; +-identityˡ; +-identityʳ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Sovereign.Algebra.LaurentCanon
  using (LaurentTerm; Laurent; Canon; canon-nil; canon-one; canon-cons;
         canon-tail; canon-<-head; InT; here; there)
open import Sovereign.Algebra.LaurentNorm
  using (insertCᵌ; Cmp3; cmp3; lt3; eq3; gt3)

-- ────────────────────────────────────────────────────────────────────
-- 序工具（复用 LaurentNorm 的形式；此处独立给出以保持模块自足）
-- ────────────────────────────────────────────────────────────────────

-- 项的系数 / 指数投影（缩写）
cf : LaurentTerm → ℤ
cf = proj₁
ex : LaurentTerm → ℤ
ex = proj₂

-- ────────────────────────────────────────────────────────────────────
-- sums：逐指数系数和；δ：插入项的贡献
-- ────────────────────────────────────────────────────────────────────

sums : LaurentTerm → Laurent → ℤ
sums u [] = + 0
sums u ((c , n) ∷ ts) with ex u ≟ n
... | yes _ = c + sums u ts
... | no _  = sums u ts

δ : LaurentTerm → LaurentTerm → ℤ
δ u (c , n) with ex u ≟ n
... | yes _ = c
... | no _  = + 0

-- 可加性：拼接的和 = 和的和（foldr 拆分）
sums-++ : ∀ (u : LaurentTerm) xs ys →
  sums u (xs ++ ys) ≡ sums u xs + sums u ys
sums-++ u [] ys = sym (+-identityˡ (sums u ys))
sums-++ u ((c , n) ∷ xs) ys with ex u ≟ n
... | yes _ =
  trans (cong (λ w → c + w) (sums-++ u xs ys))
        (sym (+-assoc c (sums u xs) (sums u ys)))
... | no _ = sums-++ u xs ys

-- ────────────────────────────────────────────────────────────────────
-- ℤ 洗牌引理（eq 分支用）
-- ────────────────────────────────────────────────────────────────────

-- S + (c_t + c_x) ≡ (c_x + S) + c_t
sums-shuffle : ∀ S c_x c_t →
  S + (c_t + c_x) ≡ (c_x + S) + c_t
sums-shuffle S c_x c_t =
  trans (+-comm S (c_t + c_x))
  (trans (+-assoc (c_t + c_x) S c_t)
  (trans (cong (_+ c_t) (sym (+-assoc c_t c_x S)))
  (trans (cong (_+ c_t) (cong (λ w → c_t + w) (+-comm c_x S)))
  (trans (+-assoc c_t S c_t)
  (trans (cong (_+ c_t) (+-comm c_t S))
         (+-assoc S c_t c_t))))))

-- 零和：dx + dt ≡ + 0 ⟹ S ≡ (dx + S) + dt
--   证明：S ≡ (dx + dt) + S [identityˡ + cong] ≡ dx + (dt + S)
--         [assoc] ≡ dx + (S + dt) [comm(内)] ≡ (dx + S) + dt [assoc]
zero-shuffle : ∀ S dx dt → dx + dt ≡ + 0 → S ≡ (dx + S) + dt
zero-shuffle S dx dt z =
  trans (+-identityˡ S)
  (trans (cong (_+ S) (sym z))
  (trans (sym (+-assoc dx dt S))
  (trans (cong (λ w → dx + w) (+-comm dt S))
         (+-assoc dx S dt))))

-- ────────────────────────────────────────────────────────────────────
-- 核心引理：插入保持逐指数和（对 Canon 结构归纳）
-- ────────────────────────────────────────────────────────────────────

insertCᵌ-sums : ∀ (u t : LaurentTerm) ts → Canon ts →
  sums u (proj₁ (proj₁ (insertCᵌ t ts))) ≡ sums u ts + δ u t
insertCᵌ-sums u t [] c =
  trans (+-identityʳ (δ u t)) (sym (+-identityˡ (δ u t)))
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  with cmp3 (ex t) (ex x)
... | gt3 _ _ g =
  trans (cong (δ u t +_) (+-identityʳ (δ u x)))
        (sym (trans (cong (_+ (δ u x)) (+-identityʳ (δ u t)))
                    (+-comm (δ u t) (δ u x))))
... | lt3 _ _ l =
  trans (cong (δ u x +_) (+-identityʳ (δ u t)))
        (sym (trans (+-assoc (δ u x) (+ 0) (δ u t))
                    (cong (δ u x +_) (+-identityˡ (δ u t)))))
... | eq3 _ _ e with (cf t + cf x) ≟ + 0
...   | yes z with ex u ≟ ex x
...     | yes ux = trans (cong (_+ (+ 0)) (cong cf ux))
                      (sym (trans (cong (_+ (+ 0)) (cong cf (sym e)))
                                  (trans (cong (_+ (cf x)) (cong cf ux))
                                         (+-comm (cf x) (cf t)))))
...     | no ux = refl
insertCᵌ-sums u t (x ∷ []) (canon-one .x)
  | eq3 _ _ e
  | no nlt with ex u ≟ ex x
...   | yes ux = trans (+-identityʳ (δ u t))
                     (sym (trans (cong (_+ (δ u t)) (+-identityˡ (δ u x)))
                                 (cong (λ w → δ u x + w) (sym (cong cf ux)))))
...   | no ux = refl
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  with cmp3 (ex t) (ex x)
... | gt3 _ _ g = +-comm (sums u (x ∷ x₂ ∷ xs)) (δ u t)
... | eq3 _ _ e with (cf t + cf x) ≟ + 0
...   | yes z = refl
...   | no _ with ex u ≟ ex x
...     | yes ux =
  trans (insertCᵌ-sums u (cf t + cf x , ex t) (x₂ ∷ xs) s)
        (sums-shuffle (sums u (x₂ ∷ xs)) (cf x) (cf t))
...     | no ux =
  let IH = insertCᵌ-sums u (cf t + cf x , ex t) (x₂ ∷ xs) s in
  trans IH
  (trans (cong (_+ (δ u t)) (sym (+-identityˡ (sums u (x₂ ∷ xs)))))
         (trans (cong (_+ (+ 0)) (sym (+-identityʳ (δ u t))))
                (+-identityʳ (sums u (x₂ ∷ xs)))))
insertCᵌ-sums u t (x ∷ x₂ ∷ xs) (canon-cons .x .x₂ .xs p s)
  | lt3 _ _ l with insertCᵌ t (x₂ ∷ xs) s
...   | (w' , cw' , dj') =
  trans (cong (δ u x +_) (insertCᵌ-sums u t (x₂ ∷ xs) s))
        (sym (+-assoc (δ u x) (sums u (x₂ ∷ xs)) (δ u t)))
