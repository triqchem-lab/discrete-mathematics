{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Foundation.FirstHit
-- ℕ 上「界内首个命中」搜索（通用有界搜索引理族）——对界结构递归，无良基递归。
--
-- 数学背景：给定可判定谓词 P : ℕ → Set 与界 bound，返回
--     Σ ℕ (λ k → k ≤ bound × P k × 最小性) ⊎ (∀ m → m ≤ bound → ¬ P m)
--   即「最小命中 k（带界内最小性证据）」或「界内全无命中」的析取。
--
-- 核心原则：
--   1. **对界 bound 结构归纳**（zero 案 + suc 案递归），不需见证输入；
--   2. **命中/无命中析取形**：区分返回避免空目标卡死（prover_limits: agda-empty-goal-ton-stuck 绕行——原 searchFin 返回结构证最小性的 subst 卡 toℕ 不归约）；
--   3. 无 funExt；0 postulate / 0 hole。
--
-- 来源：原居 Algebra.GroupTheory.CosetConstruction §3a（2026-10-11 波 2 接口抽取——
--   通用件下沉 Foundation 层，消除 Tarski←CosetConstruction 逆向边；三消费者同源零重证）。
--
-- 包含：≤-suc-split｜none-zero｜lift-first｜top-min｜no-hit｜firstIn-tail｜firstIn

module Sovereign.Foundation.FirstHit where

open import Data.Nat using (ℕ; _≤_; z≤n; s≤s; suc; zero)
open import Data.Nat.Properties using (m≤n⇒m≤1+n; ≤-refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Negation.Core using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- m ≤ suc n 的二分
≤-suc-split : ∀ {m n : ℕ} → m ≤ suc n → (m ≤ n) ⊎ (m ≡ suc n)
≤-suc-split {zero}  z≤n       = inj₁ z≤n
≤-suc-split {suc m} {zero}  (s≤s z≤n) = inj₂ refl
≤-suc-split {suc m} {suc n} (s≤s m≤sn) with ≤-suc-split {m} {n} m≤sn
... | inj₁ m≤n  = inj₁ (s≤s m≤n)
... | inj₂ refl = inj₂ refl

-- 界为 0 时唯一元素是 0
none-zero : ∀ (P : ℕ → Set) → ¬ P zero → ∀ m → m ≤ zero → ¬ P m
none-zero P ¬p0 zero    z≤n = ¬p0
none-zero P ¬p0 (suc _) ()

-- 命中分支：界内最小 ⇒ 对 suc b 内的元素也最小
lift-first : ∀ (P : ℕ → Set) {k b m : ℕ}
           → k ≤ b → (m ≤ b → P m → k ≤ m) → (m ≤ b) ⊎ (m ≡ suc b) → P m → k ≤ m
lift-first P k≤b h (inj₁ m≤b)  pm = h m≤b pm
lift-first P k≤b h (inj₂ refl) pm = m≤n⇒m≤1+n k≤b

-- 本界顶部命中：对界内任意满足者都 ≤（下方满足者与假设矛盾）
top-min : ∀ (P : ℕ → Set) {b m : ℕ}
        → (m ≤ b → ¬ P m) → (m ≤ b) ⊎ (m ≡ suc b) → P m → suc b ≤ m
top-min P h (inj₁ m≤b)  pm = ⊥-elim (h m≤b pm)
top-min P h (inj₂ refl) pm = ≤-refl

-- 全界无命中
no-hit : ∀ (P : ℕ → Set) {b m : ℕ}
       → (m ≤ b → ¬ P m) → ¬ P (suc b) → (m ≤ b) ⊎ (m ≡ suc b) → P m → ⊥
no-hit P h ¬psb (inj₁ m≤b)  pm = h m≤b pm
no-hit P h ¬psb (inj₂ refl) pm = ¬psb pm

-- 下半界无命中时，判定本界顶部
firstIn-tail : ∀ (P : ℕ → Set) (b : ℕ) → (∀ m → m ≤ b → ¬ P m) → Dec (P (suc b))
             → Σ ℕ (λ k → k ≤ suc b × P k × (∀ m → m ≤ suc b → P m → k ≤ m))
             ⊎ (∀ m → m ≤ suc b → ¬ P m)
firstIn-tail P b noneb (yes psb) =
  inj₁ (suc b , (≤-refl , (psb , λ m m≤sb pm → top-min P (noneb m) (≤-suc-split m≤sb) pm)))
firstIn-tail P b noneb (no ¬psb) =
  inj₂ (λ m m≤sb pm → no-hit P (noneb m) ¬psb (≤-suc-split m≤sb) pm)

-- [0, bound] 内的首个命中
firstIn : (P : ℕ → Set) (dec : ∀ m → Dec (P m)) (bound : ℕ)
        → Σ ℕ (λ k → k ≤ bound × P k × (∀ m → m ≤ bound → P m → k ≤ m))
        ⊎ (∀ m → m ≤ bound → ¬ P m)
firstIn P dec zero with dec zero
... | yes p0 = inj₁ (zero , (z≤n , (p0 , λ m _ _ → z≤n)))
... | no ¬p0 = inj₂ (none-zero P ¬p0)
firstIn P dec (suc b) with firstIn P dec b
... | inj₁ (k , (k≤b , (pk , minb))) =
      inj₁ (k , (m≤n⇒m≤1+n k≤b ,
                 (pk , λ m m≤sb pm → lift-first P k≤b (minb m) (≤-suc-split m≤sb) pm)))
... | inj₂ noneb = firstIn-tail P b noneb (dec (suc b))
