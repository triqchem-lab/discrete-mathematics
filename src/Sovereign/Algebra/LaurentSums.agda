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
  trans (sym (trans (cong (λ w → w + S) (+-comm c_x c_t))
                    (+-comm (c_t + c_x) S)))
  (trans (+-assoc c_x c_t S)
  (trans (cong (λ w → c_x + w) (+-comm c_t S))
         (sym (+-assoc c_x S c_t))))

-- 零和：dx + dt ≡ + 0 ⟹ S ≡ (dx + S) + dt
--   证明：S ≡ (dx + dt) + S [identityˡ + cong] ≡ dx + (dt + S)
--         [assoc] ≡ dx + (S + dt) [comm(内)] ≡ (dx + S) + dt [assoc]
zero-shuffle : ∀ S dx dt → dx + dt ≡ + 0 → S ≡ (dx + S) + dt
zero-shuffle S dx dt z =
  sym (trans (+-assoc dx S dt)
  (trans (cong (λ w → dx + w) (+-comm S dt))
  (trans (sym (+-assoc dx dt S))
  (trans (cong (_+ S) z)
         (+-identityˡ S)))))
-- ────────────────────────────────────────────────────────────────────
-- 核心引理：插入保持逐指数和（对 Canon 结构归纳）
-- ────────────────────────────────────────────────────────────────────

-- insertCᵌ-sums（插入的逐指数和不变量）待下一轮实现。
-- 设计决策（Round-6 定型）：插入项 t 的贡献统一写成 sums u (t ∷ [])
-- （δ 与 sums 是两个函数，其内部 with-aux 互不精炼——本会话实测）；
-- 陈述：sums u (proj₁ (insertCᵌ t ts c)) ≡ sums u ts + sums u (t ∷ [])
-- 各分支方程清单：
--   nil        : refl 侧 = sym identityˡ
--   one-gt/lt3 : assoc/identityʳ 洗牌（无 u≟x 情形）
--   one-eq-yes : z(系数和为零) + u≟x 情形 + comm/identity
--   one-eq-no  : comm + identity（m 的指数 = exp t 定义相等）
--   cons-gt    : +-comm
--   cons-eq-zero : refl（结果 = ts 原样）
--   cons-eq-no : IH + sums-shuffle（u≟x 情形）+ zero-shuffle（no 情形）
--   cons-lt3   : cong + sym assoc（无 u≟x 情形）