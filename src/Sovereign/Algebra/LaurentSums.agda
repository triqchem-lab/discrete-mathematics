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

-- insertCᵌ-sums（插入的逐指数和不变量）待实现。
-- 设计定型（Round-10/11）：直接对 insertCᵌ 的调用结果证 sums 方程会因
-- 跨函数 with-精炼失败（insertCᵌ 的内部 with 与证明的 with 不互精炼，
-- 本会话实测 gt3/yes/no 情形）。定型方案：SpecT 携带方程分量
--   sumsEq : ∀ u → sums u w ≡ sums u ts + sums u (t ∷ [])
-- （u 在分量内量化，SpecT 保持无 u 依赖），insertCᵌ 各分支按归纳直接证，
-- C-分支用内层 spec 的 sumsEq（递归 IH），B-分支用 bt-cancel/bt-exeq
-- 证零和恒等（zero-shuffle 模式）。随后 insertCᵌ-sums = 一行取分量。
-- 待办详见 journal Round-11。
