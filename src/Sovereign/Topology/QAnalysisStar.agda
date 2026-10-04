{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.QAnalysisStar
-- 任务书第二层·2.3 + 2.2 交叉：星形连通的**泛型化**（QStarAnalysis）
--
-- 数学背景：McCordCore 定理 A（锥形连通核）——有全局最小元 ⊥ 的有限
--   偏序集，比较图上任意两点有长度 ≤ 2 的路径（x → ⊥ → y）。本模块把
--   该构造从「比较图 + HasBottom」泛化为 QAnalysis 的**星形扩展**：
--
--   QStarAnalysis record（展示群风格：定律为 record 字段）：
--     center   : A                     —— 星形中心（锥顶）
--     star     : ∀ x → Shared x c      —— 全员共享中心（单字段即可，
--                                        反方向经 share-sym 导出）
--
--   泛型定理 star-connects：任意两点 2 步路径（qstep 两次 + qnil）。
--
--   双实例：
--   ①McCord 2-链：cmpEdge + HasBottom（复用 McCordCore）——star x = inj₁ (bot x)
--   ②Face3 面：FaceShare3+ 包装（含自返构造子），center = F0
--     （F0=[1,2] 与 F1/F2 均共享，自身自返）
--
-- 复用：QAnalysisRecord（泛型接口）+ McCordCore（HasBottom/bot）
--       + QAnalysisFacesInstance（FaceShare3/sym）
--
-- 0 postulate / 0 hole。
module Sovereign.Topology.QAnalysisStar where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Sovereign.Topology.QAnalysisRecord
  using (QAnalysis; QPathR; qreflR; share→path; qtransR; qsymR; qstep; qnil)
open import Sovereign.Topology.AlexandroffFinite
  using (FinitePoset; chain2; chain2-⊑)
open import Sovereign.Topology.McCordCore using (HasBottom; cmpEdge)

--------------------------------------------------------------------------------
-- §1. QStarAnalysis record（QAnalysis + 星形中心两字段）
--------------------------------------------------------------------------------

record QStarAnalysis (A : Set) : Set₁ where
  field
    base    : QAnalysis A             -- 底层 Q-analysis（Shared + share-sym）
    center  : A                       -- 星形中心（锥顶）
    star    : ∀ x → QAnalysis.Shared base x center  -- 全员共享中心（定律字段）

--------------------------------------------------------------------------------
-- §2. 泛型定理：星形连通（任意两点 2 步路径）
--
--   x → c（star x）→ y（share-sym (star y) 翻转）——McCord 定理 A 的
--   泛型化：锥形连通核在任意 QAnalysis 上成立（给 star 字段即可）。
--------------------------------------------------------------------------------

star-connects : ∀ {A : Set} (qa : QStarAnalysis A) (x y : A) →
                QPathR (QStarAnalysis.base qa) x y
star-connects {A} qa x y =
  qstep (QStarAnalysis.center qa)
        (QStarAnalysis.star qa x)
        (qstep y
           (QAnalysis.share-sym (QStarAnalysis.base qa) (QStarAnalysis.star qa y))
           (qnil refl))

--------------------------------------------------------------------------------
-- §3. 实例一：McCord 2-链（cmpEdge + HasBottom）
--
--   center = ⊥ = fzero；star x = inj₁ (bot x)（⊑ 方向：⊥ ⊑ x）
--------------------------------------------------------------------------------

mccord-chain2-base : QAnalysis (Fin 2)
mccord-chain2-base = record { Shared = cmpEdge chain2 ; share-sym = sym-cmp }
  where
    sym-cmp : ∀ {x y} → cmpEdge chain2 x y → cmpEdge chain2 y x
    sym-cmp (inj₁ h) = inj₂ h
    sym-cmp (inj₂ h) = inj₁ h

mccord-chain2 : QStarAnalysis (Fin 2)
mccord-chain2 = record
  { base   = mccord-chain2-base
  ; center = fzero
  ; star   = λ x → inj₂ (chain2-bot x)
  }
  where
    chain2-bot : ∀ x → FinitePoset._⊑_ chain2 fzero x
    chain2-bot x = inj₁ refl

-- 核对：2-链两点 2 步路径（McCordCore 定理 A 的泛型重演）
mccord-star-check : QPathR mccord-chain2-base (fsuc fzero) (fsuc fzero)
mccord-star-check = star-connects mccord-chain2 (fsuc fzero) (fsuc fzero)

--------------------------------------------------------------------------------
-- §4. 实例二：Face3 面（FaceShare3+ 包装含自返，center = F0）
--------------------------------------------------------------------------------

open import Sovereign.Topology.QAnalysisFacesInstance
  using (Face3; F0; F1; F2; FaceShare3; faces-share-sym; fs-10; fs-20)

-- FaceShare3+：自返构造子 + 交叉提升（避免修改已证模块）
data FaceShare3+ : Face3 → Face3 → Set where
  fs+-refl  : ∀ a → FaceShare3+ a a
  fs+-cross : ∀ {a b} → FaceShare3 a b → FaceShare3+ a b

faces-share-sym+ : ∀ {a b : Face3} → FaceShare3+ a b → FaceShare3+ b a
faces-share-sym+ (fs+-refl a) = fs+-refl a
faces-share-sym+ (fs+-cross s) = fs+-cross (faces-share-sym s)

faces-base : QAnalysis Face3
faces-base = record { Shared = FaceShare3+ ; share-sym = faces-share-sym+ }

-- center = F0：F0=[1,2] 与 F1/F2 共享（fs-10/fs-20 提升为 cross），自身自返
faces-star : QStarAnalysis Face3
faces-star = record
  { base   = faces-base
  ; center = F0
  ; star   = λ x → star-aux x
  }
  where
    star-aux : ∀ x → FaceShare3+ x F0
    star-aux F0 = fs+-refl F0
    star-aux F1 = fs+-cross fs-10
    star-aux F2 = fs+-cross fs-20

-- 核对：F1 → F0 → F2 两步路径
faces-star-check : QPathR faces-base F1 F2
faces-star-check = star-connects faces-star F1 F2
