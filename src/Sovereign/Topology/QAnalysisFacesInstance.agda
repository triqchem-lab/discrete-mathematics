{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.QAnalysisFacesInstance
-- 任务书第二层·2.3 深化：lin3 面共享的 QAnalysis 实例
--
-- 数学背景：QAnalysisRecord 的泛型 QAnalysis record 在此以 lin3 序复形
--   面实例化。载体用**枚举 data Face3**（face0/1/2 的三面——展示群
--   「生成元用 data」风格；避免函数类型 Fin 2 → Fin 3 在 cubical 下的
--   未解 meta 约束），共享关系同为 data（三对共享顶点）。
--
--   语义锚（注释层）：F0 ≙ face0=[1,2]、F1 ≙ face1=[0,2]、F2 ≙ face2=[0,1]
--   （函数层定义在 OrderComplexFaces，其 IsChain 合法性已证）
--
-- 复用：QAnalysisRecord.QAnalysis/QPathR/qreflR/share→path/qtransR
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.QAnalysisFacesInstance where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.QAnalysisRecord
  using (QAnalysis; QPathR; qreflR; share→path; qtransR)

--------------------------------------------------------------------------------
-- §1. 载体：三面枚举（data——展示群生成元风格）
--------------------------------------------------------------------------------

data Face3 : Set where
  F0 F1 F2 : Face3

--------------------------------------------------------------------------------
-- §2. 共享关系：三对共享顶点（data 枚举）
--   F0=[1,2] 与 F1=[0,2] 共享顶点 2
--   F1=[0,2] 与 F2=[0,1] 共享顶点 0
--   F2=[0,1] 与 F0=[1,2] 共享顶点 1
--------------------------------------------------------------------------------

data FaceShare3 : Face3 → Face3 → Set where
  fs-01 : FaceShare3 F0 F1
  fs-10 : FaceShare3 F1 F0
  fs-12 : FaceShare3 F1 F2
  fs-21 : FaceShare3 F2 F1
  fs-20 : FaceShare3 F2 F0
  fs-02 : FaceShare3 F0 F2

-- 对称性定律（六分支两两翻转，全部构造子直配）
faces-share-sym : ∀ {a b : Face3} → FaceShare3 a b → FaceShare3 b a
faces-share-sym fs-01 = fs-10
faces-share-sym fs-10 = fs-01
faces-share-sym fs-12 = fs-21
faces-share-sym fs-21 = fs-12
faces-share-sym fs-20 = fs-02
faces-share-sym fs-02 = fs-20

--------------------------------------------------------------------------------
-- §3. QAnalysis 实例
--------------------------------------------------------------------------------

lin3-faces : QAnalysis Face3
lin3-faces = record { Shared = FaceShare3 ; share-sym = faces-share-sym }

--------------------------------------------------------------------------------
-- §4. 展示群核对
--------------------------------------------------------------------------------

-- qrefl 闭合
lin3-refl-check : QPathR lin3-faces F0 F0
lin3-refl-check = qreflR lin3-faces F0

-- 共享→路径（F0 → F1）
path-f0f1 : QPathR lin3-faces F0 F1
path-f0f1 = share→path lin3-faces fs-01

-- 传递拼接（F0 → F1 → F2）
path-f0f2 : QPathR lin3-faces F0 F2
path-f0f2 = qtransR lin3-faces path-f0f1 (share→path lin3-faces fs-12)

-- 对称拼接（F0 → F1 → F0，经 qsymR 依赖 share-sym 字段）
path-f0f1f0 : QPathR lin3-faces F0 F0
path-f0f1f0 = qtransR lin3-faces path-f0f1 (qsymR-path-f1f0)
  where
    qsymR-path-f1f0 : QPathR lin3-faces F1 F0
    qsymR-path-f1f0 = share→path lin3-faces (faces-share-sym fs-01)
