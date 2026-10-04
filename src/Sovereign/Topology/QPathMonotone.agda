{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.QPathMonotone
-- 任务书第二层·2.3 深化：q 层级**单调性定理**（泛型）
--
-- 数学背景：Atkin Q-analysis 的核心层级性质——若高层共享关系蕴含
--   低层共享关系（S₁ a b ⟹ S₀ a b），则高层连通路径可**逐层翻译**为
--   低层连通路径。即「q=1 连通 ⟹ q=0 连通」的一般形式：
--   连通性随关系单调递增（关系越强、路径越多）。
--
--   泛型定理 qpath-mono：对任意关系包含 (∀ a b → S₁ a b → S₀ a b)，
--   QPathG A S₁ a b → QPathG A S₀ a b（对路径结构归纳）。
--
--   实例化（双三角）：边共享 FaceShare2（q=1）蕴含顶点共享 VShare2
--   （q=0）——ΔL/ΔR 共享边 [1,2] 则共享顶点 1 与 2。
--
-- 复用：QAnalysisRecord.QPathG（泛型 data）
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.QPathMonotone where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.QAnalysisRecord using (QPathG; qnil; qstep)

--------------------------------------------------------------------------------
-- §1. 泛型单调性定理：关系包含 ⟹ 路径可翻译
--
--   证明：对路径结构归纳——qnil 保持（等式与关系无关）；
--   qstep c s p 的共享步 s : S₁ a c 经包含翻译为 S₀ a c，尾递归翻译。
--------------------------------------------------------------------------------

qpath-mono : ∀ (A : Set) (S₁ S₀ : A → A → Set) →
             (∀ a b → S₁ a b → S₀ a b) →
             ∀ {a b} → QPathG A S₁ a b → QPathG A S₀ a b
qpath-mono A S₁ S₀ incl (qnil refl) = qnil refl
qpath-mono A S₁ S₀ incl (qstep c s p) =
  qstep c (incl _ c s) (qpath-mono A S₁ S₀ incl p)

--------------------------------------------------------------------------------
-- §2. 双三角实例化：边共享（q=1）蕴含顶点共享（q=0）
--
--   语义锚：TL ≙ ΔL=[0,1,2]、TR ≙ ΔR=[1,2,3]，共享边 [1,2]。
--------------------------------------------------------------------------------

data Tri2 : Set where
  TL TR : Tri2

-- q=1：边共享（复用 QAnalysisTwoTriangles 的结构，本模块独立枚举）
data EdgeShare2 : Tri2 → Tri2 → Set where
  es : EdgeShare2 TL TR

-- q=0：顶点共享（共享顶点 1 或 2——枚举）
data VertexShare2 : Tri2 → Tri2 → Set where
  vs-v1  : VertexShare2 TL TR
  vs-v2  : VertexShare2 TL TR
  vs-v1' : VertexShare2 TR TL
  vs-v2' : VertexShare2 TR TL

-- 对称性（顶点共享，四分支两两翻转）
vertex-share-sym : ∀ {a b : Tri2} → VertexShare2 a b → VertexShare2 b a
vertex-share-sym vs-v1  = vs-v1'
vertex-share-sym vs-v2  = vs-v2'
vertex-share-sym vs-v1' = vs-v1
vertex-share-sym vs-v2' = vs-v2

-- 关系包含：边共享 ⟹ 顶点共享（共享边 [1,2] 则共享顶点 1 与 2）
edge⟶vertex : ∀ a b → EdgeShare2 a b → VertexShare2 a b
edge⟶vertex TL TR es = vs-v1

--------------------------------------------------------------------------------
-- §3. 实例定理：q=1 路径 ⟹ q=0 路径（单调性翻译）
--------------------------------------------------------------------------------

-- q=1 路径（TL → TR 经边）
q1-path : QPathG Tri2 EdgeShare2 TL TR
q1-path = qstep TR es (qnil refl)

-- 翻译为 q=0 路径（单调性定理实例）
q0-path : QPathG Tri2 VertexShare2 TL TR
q0-path = qpath-mono Tri2 EdgeShare2 VertexShare2 edge⟶vertex q1-path

-- 对偶核对：q=0 路径也可直接构造（共享顶点 1）
q0-path-direct : QPathG Tri2 VertexShare2 TL TR
q0-path-direct = qstep TR vs-v1 (qnil refl)
