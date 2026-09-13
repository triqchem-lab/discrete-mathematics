{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Trust.ReductionGapWitness — 「展示群规约缺口」的**可编译见证**（正向半边）
--
-- 完整矩阵（8 个探针的 exit 码与报错原文）见
--   `docs/techniques/presentation-reduction-gap/README.md`
-- 本模块只放**能编译**的一半（这样才有 `proof_compile` 回执）；
-- **被拒**的另一半留在那个目录里 —— 它们必须编译失败才有意义，不能进库。
--
-- 机器判定的事实（2026-09-14，Agda 2.9.0-nightly）：
--   ① **闭合实例**：已定义生成元 `step` 的 `step³ t0 ≡ t0` 由归一化器（δ/ι）直接算 ⇒ `refl`
--      （docs/ 探针 `GapProbe1`，rc=0）
--   ② **普遍定律**（变量）：`λ x → refl` 当场**被拒** ——
--      `UnequalTerms`：`step (step (step x))` 与 `x` 不等（探针 `GapProbe2b`，rc=42）
--      ⇒ 归一化器**不把关系当规则用**：这就是「展示群规约缺口」的精确形态
--   ③ **声明 `{-# REWRITE #-}` 后**，同一普遍定律**变成 `refl`**（本模块 `law-auto`）——
--      收益是自动规约，代价是关系由**命题相等**降为**定义相等**（生成元的三阶结构被**商掉**）
--      ⇒ 这正是本库「保留 δ/φ 为独立字段、不声明 REWRITE」所拒绝的那笔交易
--   ④ （docs/ 记录）该 REWRITE 对 **postulate（抽象）生成元**同样**被接受并生效**
--      （`GapProbe4` rc=0 接受、`GapProbe10` rc=0 生效）
--      ⇒ 「抽象形态连规则都写不出」**不成立**：**不商化是立场，不是技术不可能**
--
-- 与 DC 的对应：本模块的 `step` 就是 DC 幅度生成元 δ 的「已定义具体形态」；
--   · 用具体形态 ⇒ 实例可自动算，但普遍定律要证（实例逐个算 = 穷举的来历）
--   · 抽象形态（record 字段）⇒ 连实例都不算（探针 `GapProbe3`，rc=42）
--   · 声明 REWRITE ⇒ 定律自动，但结构被商掉
--   配对弹出（docs/techniques/pair-popping.md）是「不商化」路径下的手工补偿：
--   把逐 case 穷举换成代数律重排 + 归一化器收口（本库 12/729/6561 三处已改造）。

module Sovereign.Trust.ReductionGapWitness where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Agda.Builtin.Equality.Rewrite

--------------------------------------------------------------------------------
-- 一个**已定义**的三阶生成元（对照 DC 的 δ：阶 3）
--------------------------------------------------------------------------------

data T3 : Set where
  t0 t1 t2 : T3

step : T3 → T3
step t0 = t1
step t1 = t2
step t2 = t0

--------------------------------------------------------------------------------
-- ① 闭合实例：归一化器自己算，不需要任何规则
--------------------------------------------------------------------------------

closed-instance : step (step (step t0)) ≡ t0
closed-instance = refl

--------------------------------------------------------------------------------
-- ③ 把关系声明成 REWRITE ⇒ 普遍定律变成 refl（对照：不声明时被拒，见 docs/ GapProbe2b）
--------------------------------------------------------------------------------

-- 关系本身先证出来（3 个 case = 穷举；这正是「缺统一规约」时唯一的路）
step-3-law : ∀ x → step (step (step x)) ≡ x
step-3-law t0 = refl
step-3-law t1 = refl
step-3-law t2 = refl

{-# REWRITE step-3-law #-}

-- 声明之后：**同一个命题不再需要证明**（定义相等了）—— 商化的收益
--   注意：这条 `refl` 在声明 REWRITE **之前**写不出来（机器判定：UnequalTerms）
law-auto : ∀ x → step (step (step x)) ≡ x
law-auto = λ x → refl

-- 0 postulate / 0 hole。
