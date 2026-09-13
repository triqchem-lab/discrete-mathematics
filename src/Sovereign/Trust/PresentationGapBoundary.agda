{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.PresentationGapBoundary — 「缺口形式化」的**边界**（哪些能写成命题，哪些不能）
--
-- 用户提案（2026-09-14）：
--   record PresentationReductionGap : Set₁ where
--     field presentation : GroupPresentation
--           no-automatic-reduction :
--             ∀ p → ¬ (IsDefinitionallyEqual (δ (δ (δ p))) p)
--
-- 本模块用 Agda 裁决这个提案的**可陈述性**，结论分三层：
--
--   ① **朴素内部编码是自相矛盾的**（可反证）：若把 `IsDefinitionallyEqual` 读成内部的 `_≡_`，
--      则对展示群（δ³ 是 record 字段）该 `¬` 字段**给得出居留元的反证**——
--      只要载体非空即可反证（`naive-encoding-refuted`）。所以这种写法不是「精确陈述缺口」，
--      而是把一个真命题（δ³ 成立）的否定当成要求。
--
--   ② **能内部证明的是它的语义影子**：定律是**内容**而非定义——
--      存在「有 Carrier、有 δ」而定律失败的模型（`law-is-content`：Bool 上的 `not`/
--      两点上的 `flip`），故定律不可能由其余结构（也就是「定义」）逼出。
--      对照：三点上的 3-循环满足定律（`presentation-instance`）⇒ ① 的反证不是空谈。
--
--   ③ **剩下的一步只能留在元层**：从 ② 到「归一化器不能自动产生它」还需要一条**元定理**——
--      「定义相等被所有模型保持」（soundness of definitional equality）。
--      该元定理**在 Agda 内部不可陈述**（Agda 没有「定义相等」这个内部类型，
--      也无法在内部量化自己的归一化器）。因此缺口的**机器可判定证据**只能是：
--        · 反射级观察（`Agda.Builtin.Reflection` 的 `reduce` 看范式：抽象项停住 / 具体项算完），或
--        · 外部事实记录（探针的 exit 码 + 报错原文，见
--          `docs/techniques/presentation-reduction-gap/README.md`）
--      两者都不是内部定理，登记时必须标明层级。

module Sovereign.Trust.PresentationGapBoundary where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

--------------------------------------------------------------------------------
-- 展示群的**最小记录形态**（只取 δ 与 δ³；加 φ/交换律不改变本模块的结论）
--------------------------------------------------------------------------------

record DeltaPresentation : Set₁ where
  field
    Carrier : Set
    δ : Carrier → Carrier
    δ³ : ∀ c → δ (δ (δ c)) ≡ c

open DeltaPresentation

--------------------------------------------------------------------------------
-- ① 朴素内部编码（IsDefinitionallyEqual := _≡_）**可被反证**
--------------------------------------------------------------------------------

-- 用户提案的字段形态
naive-no-automatic-reduction : (p : DeltaPresentation) → Set
naive-no-automatic-reduction p = ∀ (c : Carrier p) → ¬ (δ p (δ p (δ p c)) ≡ c)

-- ① 机器判定：**只要载体非空**，该字段就不可居留
--    （因为 δ³ 正是 record 的字段，直接给出反例项）
naive-encoding-refuted : ∀ (p : DeltaPresentation) (c : Carrier p)
                       → ¬ (naive-no-automatic-reduction p)
naive-encoding-refuted p c h = h c (δ³ p c)

--------------------------------------------------------------------------------
-- ② 语义影子：定律是**内容**，不是「有函数」的推论
--------------------------------------------------------------------------------

data Two : Set where
  a b : Two

flip : Two → Two
flip a = b
flip b = a

isA : Two → Set
isA a = ⊤
isA b = ⊥

-- 存在满足「有 Carrier、有 δ」而定律**失败**的模型
--   ⇒ 定律不能由其余结构（即「定义」）逼出 —— 这是能在 Agda 内部证的那一半
law-is-content : ¬ (∀ (x : Two) → flip (flip (flip x)) ≡ x)
law-is-content h = subst isA (sym (h a)) tt

--------------------------------------------------------------------------------
-- 对照：真有 3-循环的实例（⇒ ① 的反证不是空谈）
--------------------------------------------------------------------------------

data Three : Set where
  p0 p1 p2 : Three

step : Three → Three
step p0 = p1
step p1 = p2
step p2 = p0

-- 三点上的 3-循环：定律成立（3 个 case 就是这里的**基座事实**；参见 pair-popping §2 适用判据）
step-3-law : ∀ x → step (step (step x)) ≡ x
step-3-law p0 = refl
step-3-law p1 = refl
step-3-law p2 = refl

presentation-instance : DeltaPresentation
presentation-instance = record { Carrier = Three ; δ = step ; δ³ = step-3-law }

-- 具体实例的**闭合项**：归一化器自己就能算（与抽象形态对照；抽象形态见 docs/ 探针矩阵）
closed-instance-computes : step (step (step p0)) ≡ p0
closed-instance-computes = refl

-- 0 postulate / 0 hole。
