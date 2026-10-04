{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.QAnalysisTwoTriangles
-- 任务书第二层·2.3 深化：双三角复形的 **q=1 面连通**
--
-- 数学背景：Atkin Q-analysis 的 q 层级——两个 p-单形 q-连通当且仅当
--   它们共享一个 q-面。此前实例全部是 q=0（顶点共享：Face3）。
--   本模块闭合**最小 q=1 实例**：两个 2-单形
--     ΔL = [0,1,2]、ΔR = [1,2,3]
--   共享 1-面（边）[1,2]——面间经边连通（q=1），比顶点共享高一层。
--
--   结构（全 data，展示群生成元风格）：
--     载体：Tri2 = ΔL | ΔR（两三角）
--     共享边：Edge12 = [1,2]（data 单构造子）
--     关联：E12Inc ΔL / E12Inc ΔR（边是三角的面——关联 data）
--     q=1 共享：FaceShare2（ΔL 与 ΔR 经 E12 关联——关联对存在性）
--
-- ⚠ 诚实边界：枚举 data 实例（两三角一共享边）；共享边本身作为
--   复形成员（面间对象）与一般 k 单形 roadmap。
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.QAnalysisTwoTriangles where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.QAnalysisRecord
  using (QAnalysis; QPathR; qreflR; share→path; qtransR; qsymR)

--------------------------------------------------------------------------------
-- §1. 载体：双三角枚举（data——展示群生成元风格）
--   语义锚：TL ≙ ΔL=[0,1,2]、TR ≙ ΔR=[1,2,3]
--------------------------------------------------------------------------------

data Tri2 : Set where
  TL TR : Tri2

-- 共享边 [1,2]（单构造子 data）
data Edge12 : Set where
  e12 : Edge12

--------------------------------------------------------------------------------
-- §2. 关联 data：共享边是两三角的公共 1-面
--------------------------------------------------------------------------------

data E12Inc : Tri2 → Set where
  inc-TL : E12Inc TL
  inc-TR : E12Inc TR

-- q=1 共享：存在公共关联边（TL/TR 经 E12 连通）
data FaceShare2 : Tri2 → Tri2 → Set where
  ts-edge : E12Inc TL → E12Inc TR → FaceShare2 TL TR
  ts-sym' : FaceShare2 TR TL

-- 对称性定律
tri-share-sym : ∀ {a b : Tri2} → FaceShare2 a b → FaceShare2 b a
tri-share-sym (ts-edge _ _) = ts-sym'
tri-share-sym ts-sym' = ts-edge inc-TL inc-TR

--------------------------------------------------------------------------------
-- §3. QAnalysis 实例（q=1 面连通）
--------------------------------------------------------------------------------

tri2-q : QAnalysis Tri2
tri2-q = record { Shared = FaceShare2 ; share-sym = tri-share-sym }

--------------------------------------------------------------------------------
-- §4. 展示群核对
--------------------------------------------------------------------------------

-- 共享→路径（TL → TR，经边 [1,2]——q=1 连通）
path-TL-TR : QPathR tri2-q TL TR
path-TL-TR = share→path tri2-q (ts-edge inc-TL inc-TR)

-- 对称路径（TR → TL，经 qsymR——share-sym 字段兑现）
path-TR-TL : QPathR tri2-q TR TL
path-TR-TL = qsymR tri2-q path-TL-TR

-- 往返拼接（TL → TR → TL）
path-TL-TL : QPathR tri2-q TL TL
path-TL-TL = qtransR tri2-q path-TL-TR path-TR-TL

--------------------------------------------------------------------------------
-- §5. q 层级标记：q=0（Face3 顶点共享）vs q=1（本模块边共享）
--
--   两层结构的机器可见对照：FaceShare3 的 F0↔F1 共享 0-面（顶点），
--   FaceShare2 的 TL↔TR 共享 1-面（边）——q 维度不同、机制同构。
--------------------------------------------------------------------------------

data QLevel : Set where
  q0 q1 : QLevel

-- 面共享实例的 q 层级标记
qlevel-faces : QLevel
qlevel-faces = q0

qlevel-tris : QLevel
qlevel-tris = q1
