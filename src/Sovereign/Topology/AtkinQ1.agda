{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.AtkinQAnalysis.Q1
-- 任务书第二层·2.3 延伸：Atkin Q-analysis 的 q=1 层——边连通性
--
-- 数学背景：Atkin (1972) Q-analysis 的 q=1 层分析单纯复形的**边连通性**：
--   两条边 1-连通当且仅当存在一串边使相邻两条共享一个顶点。
--   本模块在 K₃ 三角形上闭合：三条边两两共享顶点 ⟹ 全部 1-连通（单类）。
--
-- ⚠ 诚实边界：
--   1. q=1 层只处理**边**（1-单形）；更高 q 层（三角形共享边等）需要
--      单形族编码，roadmap。
--   2. K₃ 是完全图——所有边都共享顶点，连通类唯一。非完全图的多类
--      情形是 roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.AtkinQ1 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong)

--------------------------------------------------------------------------------
-- §1. 有向边表示：起点 + 终点（Fin 3 上）
--
-- 边 e = (o, d)，o = 起点（origin），d = 终点（destination）。
-- 两条边共享顶点 ⟺ 它们的 {o, d} 集合相交。
--------------------------------------------------------------------------------

record Edge : Set where
  constructor mkEdge
  field
    origin dest : Fin 3

-- Edge-share：泛型定义（用 record projection，不依赖 mkEdge 模式匹配）
Edge-share : Edge → Edge → Set
Edge-share e₁ e₂ =
  (Edge.origin e₁ ≡ Edge.origin e₂) ⊎
  ((Edge.origin e₁ ≡ Edge.dest e₂) ⊎
  ((Edge.dest e₁ ≡ Edge.origin e₂) ⊎
  (Edge.dest e₁ ≡ Edge.dest e₂)))

-- Edge-share 对称（泛型：只对 ⊎ 结构分派，不依赖 Edge 值的模式匹配）
share-sym : ∀ {e₁ e₂ : Edge} → Edge-share e₁ e₂ → Edge-share e₂ e₁
share-sym (inj₁ h) = inj₁ (sym h)
share-sym (inj₂ (inj₁ h)) = inj₂ (inj₂ (inj₁ (sym h)))
share-sym (inj₂ (inj₂ (inj₁ h))) = inj₂ (inj₁ (sym h))
share-sym (inj₂ (inj₂ (inj₂ h))) = inj₂ (inj₂ (inj₂ (sym h)))

--------------------------------------------------------------------------------
-- §2. 1-连通性：边共享关系的自反传递闭包
--------------------------------------------------------------------------------

data Q1-Path : Edge → Edge → Set where
  q1-nil  : ∀ e → Q1-Path e e
  q1-cons : ∀ e₁ e₂ e₃ → Edge-share e₁ e₂ → Q1-Path e₂ e₃ → Q1-Path e₁ e₃

-- 1-连通的传递性
q1-trans : ∀ {e₁ e₂ e₃} → Q1-Path e₁ e₂ → Q1-Path e₂ e₃ → Q1-Path e₁ e₃
q1-trans (q1-nil _) q = q
q1-trans (q1-cons a b c s p) q = q1-cons a b _ s (q1-trans p q)

-- share→path 桥接：Edge-share 直接给一步路径
share→path : ∀ {e₁ e₂ : Edge} → Edge-share e₁ e₂ → Q1-Path e₁ e₂
share→path {e₁} {e₂} s = q1-cons e₁ e₂ e₂ s (q1-nil e₂)

-- 1-连通是对称的（通过 share→path 桥接 + q1-trans 拼接）
q1-sym : ∀ {e₁ e₂} → Q1-Path e₁ e₂ → Q1-Path e₂ e₁
q1-sym (q1-nil e) = q1-nil e
q1-sym (q1-cons e₁ e₂ e₃ s p) =
  q1-trans (q1-sym p) (share→path (share-sym s))

--------------------------------------------------------------------------------
-- §3. K₃ 具体点对抗：三条边全部 1-连通
--
-- 边：e₀₁ = (0,1), e₁₂ = (1,2), e₂₀ = (2,0)
-- 共享顶点：e₀₁ ∩ e₁₂ = {1}, e₁₂ ∩ e₂₀ = {2}, e₂₀ ∩ e₀₁ = {0}
--------------------------------------------------------------------------------

e01 e12 e20 : Edge
e01 = mkEdge fzero (fsuc fzero)
e12 = mkEdge (fsuc fzero) (fsuc (fsuc fzero))
e20 = mkEdge (fsuc (fsuc fzero)) fzero

-- e₀₁ 与 e₁₂ 共享顶点 1（dest e₀₁ ≡ origin e₁₂：第三支）
share-01-12 : Edge-share e01 e12
share-01-12 = inj₂ (inj₂ (inj₁ refl))

-- e₁₂ 与 e₂₀ 共享顶点 2（dest e₁₂ ≡ origin e₂₀：第三支）
share-12-20 : Edge-share e12 e20
share-12-20 = inj₂ (inj₂ (inj₁ refl))

-- e₂₀ 与 e₀₁ 共享顶点 0（dest e₂₀ ≡ origin e₀₁：第三支）
share-20-01 : Edge-share e20 e01
share-20-01 = inj₂ (inj₂ (inj₁ refl))

-- 三条边全部 1-连通（单类见证）
k3-q1-single-class : Q1-Path e01 e12 × Q1-Path e12 e20 × Q1-Path e20 e01
k3-q1-single-class =
  ( q1-cons e01 e12 e12 share-01-12 (q1-nil e12)
  , q1-cons e12 e20 e20 share-12-20 (q1-nil e20)
  , q1-cons e20 e01 e01 share-20-01 (q1-nil e01)
  )

-- 对抗回证：对称方向也闭合
k3-q1-reverse : Q1-Path e12 e01 × Q1-Path e20 e12 × Q1-Path e01 e20
k3-q1-reverse =
  ( q1-sym (q1-cons e01 e12 e12 share-01-12 (q1-nil e12))
  , q1-sym (q1-cons e12 e20 e20 share-12-20 (q1-nil e20))
  , q1-sym (q1-cons e20 e01 e01 share-20-01 (q1-nil e01))
  )
