{-# OPTIONS --guardedness #-}

-- | _PLAMBDA —— record 字段「模式 λ vs 顶层命名件」对照验证（元评采纳件②）
--
-- 【实测结论表（8 变体独立编译，2026-10-11）】
-- | 场景 | 模式 λ | 命名件 | 判定 |
-- | 不相交子句（invol/3-cycle/Bool 反转） | GREEN | GREEN | 两形等价可用 |
-- | 递归定义（double 型） | 结构性不可表达（匿名 λ 不能自调） | GREEN | 命名件必需 |
-- | 重叠子句（字面中支+尾变支） | RED | RED | **共同陷阱**——非 λ 特有 |
-- 【归因精化】(a2) spike 教训「record 内模式 λ 卡投影合一」应修正为：
--   卡点根因 = **子句重叠 / 中性参数不可约**（两形皆卡，见 §T5 注）；
--   模式 λ 的真实局限 = **不能递归**（§T4 注）；命名件真价值 = 可归纳 + 可递归。
-- 【T5 红案留档】重叠子句形（p = zero|suc zero|suc n 三支）在两形下均 UnequalTerms
--   （中性 suc n 在字面中支与尾变支间不可决——具体报文见报告）。
-- 本件为验证性探针——结论已入报告，探针可删。

module _PLAMBDA where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- ─────────────────────────────────────────────────────────────
-- 场景 1：B3 型 presentation（involution 展示）——两形等价 GREEN
-- ─────────────────────────────────────────────────────────────
record Pres : Set where
  field
    f : ℕ → ℕ
    g : ∀ n → f (f n) ≡ n

pres-λ : Pres
pres-λ = record
  { f = λ { zero → suc zero ; (suc zero) → zero ; (suc (suc n)) → suc (suc n) }
  ; g = λ { zero → refl ; (suc zero) → refl ; (suc (suc n)) → refl }
  }

swap01 : ℕ → ℕ
swap01 zero = suc zero
swap01 (suc zero) = zero
swap01 (suc (suc n)) = suc (suc n)

swap01-invol : ∀ n → swap01 (swap01 n) ≡ n
swap01-invol zero = refl
swap01-invol (suc zero) = refl
swap01-invol (suc (suc n)) = refl

pres-named : Pres
pres-named = record { f = swap01 ; g = swap01-invol }

-- 跨 record 投影消费：两形均可引（模式 λ 投影在构造子头上可约）
pres-use-λ : ∀ n → Pres.f pres-λ (Pres.f pres-λ n) ≡ n
pres-use-λ = Pres.g pres-λ

pres-use-named : ∀ n → Pres.f pres-named (Pres.f pres-named n) ≡ n
pres-use-named = Pres.g pres-named

-- ─────────────────────────────────────────────────────────────
-- 场景 2：B2 型机件（3-循环，act³ ≡ id）——两形等价 GREEN
-- ─────────────────────────────────────────────────────────────
record Mech (A : Set) : Set where
  field
    act : A → A
    step : ∀ x → act (act (act x)) ≡ x

mech-λ : Mech ℕ
mech-λ = record
  { act = λ { zero → suc zero ; (suc zero) → suc (suc zero)
            ; (suc (suc zero)) → zero ; (suc (suc (suc n))) → suc (suc (suc n)) }
  ; step = λ { zero → refl ; (suc zero) → refl
             ; (suc (suc zero)) → refl ; (suc (suc (suc n))) → refl }
  }

cyc3 : ℕ → ℕ
cyc3 zero = suc zero
cyc3 (suc zero) = suc (suc zero)
cyc3 (suc (suc zero)) = zero
cyc3 (suc (suc (suc n))) = suc (suc (suc n))

cyc3-step : ∀ x → cyc3 (cyc3 (cyc3 x)) ≡ x
cyc3-step zero = refl
cyc3-step (suc zero) = refl
cyc3-step (suc (suc zero)) = refl
cyc3-step (suc (suc (suc n))) = refl

mech-named : Mech ℕ
mech-named = record { act = cyc3 ; step = cyc3-step }

-- ─────────────────────────────────────────────────────────────
-- 场景 3：K2Gluing 型（双映射 + 双相干）——两形等价 GREEN
-- ─────────────────────────────────────────────────────────────
data Bool : Set where
  tt ff : Bool

record Glue (A B : Set) : Set where
  field
    to : A → B
    from : B → A
    coh1 : ∀ a → from (to a) ≡ a
    coh2 : ∀ b → to (from b) ≡ b

glue-λ : Glue Bool Bool
glue-λ = record
  { to = λ { tt → ff ; ff → tt }
  ; from = λ { tt → ff ; ff → tt }
  ; coh1 = λ { tt → refl ; ff → refl }
  ; coh2 = λ { tt → refl ; ff → refl }
  }

notB : Bool → Bool
notB tt = ff
notB ff = tt

notB-invol : ∀ b → notB (notB b) ≡ b
notB-invol tt = refl
notB-invol ff = refl

glue-named : Glue Bool Bool
glue-named = record { to = notB ; from = notB ; coh1 = notB-invol ; coh2 = notB-invol }

-- ─────────────────────────────────────────────────────────────
-- 场景 4：递归定义——命名件必需（GREEN）；模式 λ 结构性不可表达
--   （匿名 λ 无名不可自调：λ { zero → zero ; (suc n) → suc (suc (???)) } 无法填）
-- ─────────────────────────────────────────────────────────────
record Stress : Set where
  field
    h : ℕ → ℕ
    comm : ∀ n → h (suc n) ≡ suc (suc (h n))

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

double-suc : ∀ n → double (suc n) ≡ suc (suc (double n))
double-suc n = refl

stress-named : Stress
stress-named = record { h = double ; comm = double-suc }

-- ─────────────────────────────────────────────────────────────
-- 场景 5（红案留档，代码注释形）：重叠子句——两形皆卡
--   形：p = λ { zero → zero ; (suc zero) → zero ; (suc n) → n }   （字面中支 + 尾变支重叠）
--       q = λ { zero → refl ; (suc n) → refl }                    （中性 suc n 不可决）
--   实测：两形（λ/命名）均 UnequalTerms——**中性参数在重叠子句间不可约**，
--   根因非模式 λ 本身，是子句设计（§T5 红案）。修法：子句构造子不相交
--   （zero | suc zero | suc (suc n) 三支），或中支改 ≥2 型。
-- ─────────────────────────────────────────────────────────────
