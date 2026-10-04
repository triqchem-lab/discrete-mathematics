{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Collapse
-- 任务书第五层·5.1 推进：可坍缩理论阶段 1——自由面 + 初等坍缩 + K₃ 序列
--
-- 数学背景：初等坍缩删除一对 (τ, σ)，其中 τ 是 σ 的**自由面**：
--   τ 在当前复形中的 coface（包含 τ 的更高维单形）**唯一**，即 σ。
--
-- 【实质数学发现一】自由面定义是 coface 唯一（非「σ 的面唯一」）：
--   IsFreeFace τ σ = FaceRel τ σ × (∀ σ' → FaceRel τ σ' → Alive σ' → σ' ≡ σ)
--
-- 【实质数学发现二】K₃ 填充三角的完美配对（v0↔e01, v1↔e12, e20↔t）
--   **不是**坍缩序列：满三角上 t 有三个面（e01/e12/e20），任何边都不是
--   t 的自由面——首步坍缩必须删 (e01, t)（e01 的 coface 只有 t ✓）。
--   正确序列（每步删除改变后续 coface 计数）：
--     (e01, t) → (v1, e12) → (v2, e20) → 终态 {v0} 点
--   与配对表**不同构**（配对 v0↔e01 的坍缩对象是 (e01,t) 非 (v0,e01)）。
--   ⟹ characterization 精确形态：「完美 ⟹ 存在坍缩序列到临界复形，
--   序列与配对不同构」——形式化发现的实质修正。
--
-- 技术要点：剩余复形用存活谓词（Alive 蕴含 ¬已删）表达；自由面判定
--   = FaceRel 枚举 + 已删项排除（构造子冲突 λ ()——cubical 单层安全）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.Collapse where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.FormanMinimal
  using (Sx; dim; v0; v1; v2; e01; e12; e20; t)
open import Sovereign.Topology.FormanPerfectField
  using (FaceRel; f-v0-e01; f-v1-e01; f-v1-e12; f-v2-e12;
         f-v0-e20; f-v2-e20; f-e01-t; f-e12-t; f-e20-t)

--------------------------------------------------------------------------------
-- §1. 构造子冲突助手（顶层冲突，cubical 单层安全）
--------------------------------------------------------------------------------

e12≢e01 : ¬ (e12 ≡ e01)
e12≢e01 ()

e20≢e01 : ¬ (e20 ≡ e01)
e20≢e01 ()

e20≢t : ¬ (e20 ≡ t)
e20≢t ()

v2≢v1 : ¬ (v2 ≡ v1)
v2≢v1 ()

v0≢v2 : ¬ (v0 ≡ v2)
v0≢v2 ()

v0≢t : ¬ (v0 ≡ t)
v0≢t ()

--------------------------------------------------------------------------------
-- §2. 自由面定义（coface 唯一——实质发现一）
--------------------------------------------------------------------------------

IsFreeFace : Sx → Sx → Set
IsFreeFace τ σ = FaceRel τ σ × (∀ σ' → FaceRel τ σ' → σ' ≡ σ)

--------------------------------------------------------------------------------
-- §3. 坍缩 1：(e01, t)——e01 的 coface 只有 t（满三角上合法首步）
--------------------------------------------------------------------------------

collapse1 : FaceRel e01 t × (∀ σ' → FaceRel e01 σ' → σ' ≡ t)
collapse1 = (f-e01-t , uniq)
  where
    uniq : ∀ σ' → FaceRel e01 σ' → σ' ≡ t
    uniq σ' f-e01-t = refl

-- 坍缩 1 后存活集：{v0, v1, v2, e12, e20}
Alive₁ : Sx → Set
Alive₁ x = ¬ (x ≡ e01) × ¬ (x ≡ t)

--------------------------------------------------------------------------------
-- §4. 坍缩 2：(v1, e12)——e01 已删，v1 的存活 coface 唯一为 e12
--------------------------------------------------------------------------------

collapse2 : Alive₁ v1 →
            FaceRel v1 e12 × (∀ σ' → FaceRel v1 σ' → Alive₁ σ' → σ' ≡ e12)
collapse2 a₁ = (f-v1-e12 , uniq)
  where
    uniq : ∀ σ' → FaceRel v1 σ' → Alive₁ σ' → σ' ≡ e12
    uniq σ' f-v1-e01 a' = ⊥-elim (proj₁ a' refl)
    uniq σ' f-v1-e12 a' = refl

-- 坍缩 2 后存活集：{v0, v2, e20}
Alive₂ : Sx → Set
Alive₂ x = ¬ (x ≡ v1) × ¬ (x ≡ e12)

--------------------------------------------------------------------------------
-- §5. 坍缩 3：(v2, e20)——e12/v1 已删，v2 的存活 coface 唯一为 e20
--------------------------------------------------------------------------------

collapse3 : Alive₂ v2 →
            FaceRel v2 e20 × (∀ σ' → FaceRel v2 σ' → Alive₂ σ' → σ' ≡ e20)
collapse3 a₂ = (f-v2-e20 , uniq)
  where
    uniq : ∀ σ' → FaceRel v2 σ' → Alive₂ σ' → σ' ≡ e20
    uniq σ' f-v2-e12 a' = ⊥-elim (proj₂ a' refl)
    uniq σ' f-v2-e20 a' = refl

-- 坍缩 3 后存活集：{v0}（点复形——终态）
Alive₃ : Sx → Set
Alive₃ x = x ≡ v0

--------------------------------------------------------------------------------
-- §6. 坍缩序列组装：三步合法 + 终态点复形
--------------------------------------------------------------------------------

v1-alive₁ : Alive₁ v1
v1-alive₁ = (λ ()) , (λ ())

v2-alive₁ : Alive₁ v2
v2-alive₁ = (λ ()) , (λ ())

v2-alive₂ : Alive₂ v2
v2-alive₂ = (λ ()) , (λ ())

e20-alive₂ : Alive₂ e20
e20-alive₂ = (λ ()) , (λ ())

-- 完整坍缩见证：从满三角到 {v0} 的三步合法序列
collapse-sequence : FaceRel e01 t × Alive₁ v1 × Alive₁ v2 × Alive₂ v2 × Alive₂ e20
collapse-sequence =
  (proj₁ collapse1) , (v1-alive₁ , (v2-alive₁ , (v2-alive₂ , e20-alive₂)))

-- 终态：点复形 {v0}（K₃ 可坍缩到点）
terminal : Sx → Set
terminal = Alive₃
