{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Analysis.Finiteness.Tarski
-- 任务书第一层·1.3：Tarski-Kuratowski 极小元原理（1920–1924）在 Fin n 上的实例
--
-- 数学背景：Tarski 1924 / Kuratowski 1920 —— S 有限 ⟺ 非空子集族有极小元。
--   经典版量化幂集（连续统装置，见 Foundations 头注对照）；本层只做**型有限载体
--   上的可判定实例**：Fin n 的非空可判定子集族有 toℕ 最小元。与 Dedekind 版的
--   双向等价（需经典逻辑）不入本库 —— 缺口声明见 FinitenessZoo §5。
--
-- 复用：CosetConstruction.firstIn（对界结构递归的首个命中 + 极小性；不用
--   searchFin 返回结构 —— 库内教训 agda-empty-goal-ton-stuck）。
--   修复注（2026-10-02 沙盒实证）：firstIn 界取 n（非已知见证的 toℕ i），min 覆盖
--   全体 Fin n 的 toℕ，免分支；roundtrip 混用坑：ℕ 侧用 toℕ-fromℕ<、Fin 侧用
--   fromℕ<-toℕ（第一参 i : Fin n 把界钉死在 n）。
--
-- 0 postulate / 0 hole。
module Sovereign.Analysis.Finiteness.Tarski where

open import Data.Nat using (ℕ; _<_; _≤_)
open import Data.Nat.Properties using (_<?_; <⇒≤)
open import Data.Fin using (Fin; toℕ; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-fromℕ<; fromℕ<-toℕ)
open import Data.Product using (_×_; _,_; Σ)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import Sovereign.Algebra.GroupTheory.CosetConstruction using (firstIn)

-- Fin n 上非空可判定子集族有 toℕ 最小元
tarski-min : ∀ (n : ℕ) (P : Fin n → Set) (dec : ∀ i → Dec (P i)) →
             Σ (Fin n) P →
             Σ (Fin n) (λ k → P k × (∀ j → P j → toℕ k ≤ toℕ j))
tarski-min n P dec (i , pi) with firstIn (λ m → Σ (m < n) (λ m<n → P (fromℕ< m<n)))
                                         (λ m → dec-m m) n
  where
    dec-m : ∀ m → Dec (Σ (m < n) (λ m<n → P (fromℕ< m<n)))
    dec-m m with m <? n
    ... | yes m<n with dec (fromℕ< m<n)
    ...   | yes pm = yes (m<n , pm)
    ...   | no ¬pm = no (λ (_ , p) → ¬pm p)
    dec-m m | no ¬m<n = no (λ (m<n , _) → ¬m<n m<n)
... | inj₁ (k , _ , (k<n , pk) , min) =
  (fromℕ< k<n) , (pk , λ j pj →
    subst (λ x → x ≤ toℕ j)
          (sym (toℕ-fromℕ< k<n))
          (min (toℕ j) (<⇒≤ (toℕ<n j)) (toℕ<n j , subst P (sym (fromℕ<-toℕ j (toℕ<n j))) pj)))
... | inj₂ none = ⊥-elim (none (toℕ i) (<⇒≤ (toℕ<n i)) (toℕ<n i , subst P (sym (fromℕ<-toℕ i (toℕ<n i))) pi))
