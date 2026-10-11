{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.WellFounded
-- 良基关系与 Noetherian 归纳原理
--
-- 数学背景：关系 R 良基（well-founded）当且仅当无无限严格下降链——
-- 等价地每个元素都被归纳原理覆盖（Acc 形）。Noetherian 归纳是数学归纳法
-- 的关系版：证明 P x 只需「所有严格前驱满足 P 则 x 满足 P」。这是 Coq
-- Wellfounded / stdlib Induction.WellFounded 的核心内容；本模块以 stdlib
-- 的 Acc/WellFounded 为信任基座直用，自证**归纳原理主件** wf-ind 与
-- 自然数强归纳实例 nat-strong-ind。
--
-- 与库内件的关系（衔接注记）：Topology.StongCore 的 beat point 消去
-- 「收缩可消点不改同伦型」，其递减度量的终止性正是良基性——beat point
-- 序列必终止 ⟺ 消去序良基。（注：层方向 Foundation ← Topology 反向，
-- 故仅注记衔接不 import——依赖方向纪律。）
--
-- 核心原则：
-- 1. stdlib 直用（Acc/acc/WellFounded/<-wellFounded 为信任基座）
-- 2. wf-ind = 本模块主件（Acc 递归构造性展开——零新公理）
-- 3. 0 postulate / 0 hole
--
-- 包含：wf-ind（Noetherian 归纳原理）· nat-strong-ind（自然数强归纳）·
--       beat point 衔接注记 · 核对层

module Sovereign.Foundation.WellFounded where

open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

--------------------------------------------------------------------------------
-- ③ 基础件层：局部关系形（显式参数——与 RelationClosures 同口径）
--------------------------------------------------------------------------------

Rel : Set → Set₁
Rel A = A → A → Set

--------------------------------------------------------------------------------
-- ④ 主引理层：Noetherian 归纳原理（主件）
--------------------------------------------------------------------------------

module _ {A : Set} {R : Rel A} where

  -- Acc 归纳递归器：从良基证据出发逐点展开
  private
    go : (P : A → Set)
       → (step : ∀ x → (∀ y → R y x → P y) → P x)
       → ∀ x → Acc R x → P x
    go P step x (acc ih) = step x (λ y y≺x → go P step y (ih y≺x))

  -- Noetherian 归纳原理：良基关系上的归纳法
  -- （要证 ∀ x → P x，只需证「前驱全真 ⟹ 本点真」）
  wf-ind : WellFounded R
         → (P : A → Set)
         → (step : ∀ x → (∀ y → R y x → P y) → P x)
         → ∀ x → P x
  wf-ind wf P step x = go P step x (wf x)

--------------------------------------------------------------------------------
-- ⑤ 组合层：自然数强归纳实例（stdlib <-wellFounded 直引）
--------------------------------------------------------------------------------

-- 强归纳：要证 ∀ n → P n，只需证「所有 m < n 满足 P ⟹ n 满足 P」
nat-strong-ind : (P : ℕ → Set)
               → (step : ∀ n → (∀ m → m < n → P m) → P n)
               → ∀ n → P n
nat-strong-ind = wf-ind <-wellFounded

-- 换言之：无无限严格下降 ℕ 序列（良基性的可计算面）
-- ——beat point 消去序的终止性由同型机制承载（见头注衔接）。

--------------------------------------------------------------------------------
-- ⑥ 核对层
--------------------------------------------------------------------------------

-- 0 的 Acc 证据（无严格前驱——absurd 形收口）
check-acc0 : Acc _<_ zero
check-acc0 = acc (λ {y} ())

-- 强归纳实例核对：常真族（P ≡ ⊤——step 直通，验证 nat-strong-ind 可实例化）
trivial : ℕ → Set
trivial _ = ⊤

check-strong : ∀ n → trivial n
check-strong = nat-strong-ind trivial (λ n _ → tt)
