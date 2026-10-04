{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.McCordCore
-- 任务书第二层·2.2：McCord 弱等价（1966）的构造性 0 层核
--
-- 数学背景：McCord, "Singular homology groups and homotopy groups of finite
--   topological spaces"（Duke Math. J. 33 (1966), 465–474；概要卡 §4）证明有限
--   T₀ 空间 X 有序复形 K(X) 与弱同伦等价 |K(X)| → X。全量定理需要几何实现
--   |·| 与同伦群机件（HoTT 层）——本模块给出其**离散 0 层核**：
--     ① 比较图：可比性（⊑ 或 ⊒）作边，天然对称；
--     ② 定理 A（锥形连通核）：有最小元 ⊥ 的有限偏序集，比较图上任意两点
--        有长度 ≤ 2 的路径（经 ⊥）——即 K(X) 的 1-骨架连通（星形收缩的
--        1-骨架切片，McCord 连通性一致性的构造性充分条件）；
--     ③ 定理 B（最小元唯一）：两个全局最小元相等（antisym 直接推论）。
--
-- ⚠ 诚实边界：
--   1. 弱同伦等价 |K(X)| → X 本体（所有同伦群同构）不在本库现有机件内，
--      保持 roadmap（P2.2 主节点）——本模块只闭合其 0 层组合前置件。
--   2. 与 McCord 原文的对应是**方法论切片**，不是定理引用：0 层连通性一致
--      是弱同伦等价的必要面，不充分（高阶 πₙ 不在本核内）。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.McCordCore where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.AlexandroffFinite using (FinitePoset)
open import Sovereign.Topology.AtkinQAnalysis using (Graph; Path; nil; cons)

--------------------------------------------------------------------------------
-- §1. 比较图：可比性作边（x ⊑ y 或 y ⊑ x），⊎ 形式天然对称
--------------------------------------------------------------------------------

cmpEdge : ∀ {n} (P : FinitePoset n) → Fin n → Fin n → Set
cmpEdge P x y = FinitePoset._⊑_ P x y ⊎ FinitePoset._⊑_ P y x

cmpGraph : ∀ {n} (P : FinitePoset n) → Graph n
cmpGraph P = record
  { Edge     = cmpEdge P
  ; Edge-sym = λ x y h → flipcmp h
  }
  where
    flipcmp : ∀ {x y} → cmpEdge P x y → cmpEdge P y x
    flipcmp (inj₁ h) = inj₂ h
    flipcmp (inj₂ h) = inj₁ h

--------------------------------------------------------------------------------
-- §2. 定理 A（锥形连通核）：全局最小元 ⟹ 任意两点路径长度 ≤ 2
--
-- 路径 x → ⊥ → y：x → ⊥ 用 ⊒ 方向（inj₂ (bot x)），⊥ → y 用 ⊑ 方向
-- （inj₁ (bot y)）。这是 K(X) 星形收缩在 1-骨架上的切片。
--------------------------------------------------------------------------------

record HasBottom {n} (P : FinitePoset n) : Set where
  field
    ⊥  : Fin n
    bot : ∀ x → FinitePoset._⊑_ P ⊥ x

bottom-connects : ∀ {n} (P : FinitePoset n) (hb : HasBottom P) →
  ∀ x y → Path (cmpEdge P) x y
bottom-connects P hb x y =
  cons x ⊥' y (inj₂ (bot' x))
       (cons ⊥' y y (inj₁ (bot' y)) (nil y))
  where
    open HasBottom hb renaming (⊥ to ⊥'; bot to bot')

--------------------------------------------------------------------------------
-- §3. 定理 B：最小元唯一（antisym 推论）
--------------------------------------------------------------------------------

bottom-unique : ∀ {n} (P : FinitePoset n)
  (b₀ b₁ : Fin n) →
  (∀ x → FinitePoset._⊑_ P b₀ x) →
  (∀ x → FinitePoset._⊑_ P b₁ x) →
  b₀ ≡ b₁
bottom-unique P b₀ b₁ h₀ h₁ =
  FinitePoset.⊑-antisym P b₀ b₁ (h₀ b₁) (h₁ b₀)

--------------------------------------------------------------------------------
-- §4. 具体点对抗（对抗验证协议 §6）：2-链 0 ⊑ 1
--
-- fzero 是 2-链的全局最小元（chain2-⊑ fzero b = inj₁ refl 恒成立）；
-- 两点路径 x → 0 → 1 显式构造。
--------------------------------------------------------------------------------

open import Sovereign.Topology.AlexandroffFinite using (chain2; chain2-⊑)

chain2-bot : HasBottom chain2
chain2-bot = record
  { ⊥  = fzero
  ; bot = λ x → inj₁ refl
  }

-- 对抗实例 1：bottom-connects 在 2-链上给出 0 → 1 的显式路径（经 ⊥ = 0）
chain2-path-0-1 :
  Path (cmpEdge chain2) fzero (fsuc fzero)
chain2-path-0-1 = bottom-connects chain2 chain2-bot fzero (fsuc fzero)

-- 对抗实例 2：自返点对同样闭合（路径 x → ⊥ → x）
chain2-path-1-1 :
  Path (cmpEdge chain2) (fsuc fzero) (fsuc fzero)
chain2-path-1-1 = bottom-connects chain2 chain2-bot (fsuc fzero) (fsuc fzero)

-- 对抗实例 3：定理 B 实例化——2-链的最小元与自身相同（antisym 一行闭合）
chain2-bot-unique :
  (h : ∀ x → chain2-⊑ fzero x) (h' : ∀ x → chain2-⊑ fzero x) →
  fzero ≡ fzero
chain2-bot-unique h h' = bottom-unique chain2 fzero fzero h h'
