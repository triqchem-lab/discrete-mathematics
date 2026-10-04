{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.QAnalysisRecord
-- 任务书第二层·2.3 泛型化：Atkin Q-analysis 展示群风格泛型化
-- 展示群要求：生成元用 data，关系用 record 字段，核对 refl，0 postulate
-- 复用：AtkinQ1.Edge/share-sym（Topology/ 目录 Q-analysis 分类）
module Sovereign.Topology.QAnalysisRecord where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

--------------------------------------------------------------------------------
-- §1. 泛型连通性生成元 data
--------------------------------------------------------------------------------

data QPathG (A : Set) (S : A → A → Set) (a b : A) : Set where
  qnil  : a ≡ b → QPathG A S a b
  qstep : ∀ c → S a c → QPathG A S c b → QPathG A S a b

--------------------------------------------------------------------------------
-- §2. QAnalysis record（关系定律为 record 字段）
--------------------------------------------------------------------------------

record QAnalysis (A : Set) : Set₁ where
  field
    Shared    : A → A → Set
    share-sym : ∀ {a b} → Shared a b → Shared b a

--------------------------------------------------------------------------------
-- §3. 泛型运算
--------------------------------------------------------------------------------

QPathR : ∀ {A : Set} (qa : QAnalysis A) → A → A → Set
QPathR {A} qa = QPathG A (QAnalysis.Shared qa)

qreflR : ∀ {A : Set} (qa : QAnalysis A) (a : A) → QPathR qa a a
qreflR {A} qa a = qnil refl

share→path : ∀ {A : Set} (qa : QAnalysis A) {a b : A} →
             QAnalysis.Shared qa a b → QPathR qa a b
share→path {A} qa {a} {b} s = qstep b s (qnil refl)

qtransR : ∀ {A : Set} (qa : QAnalysis A) {a b c : A} →
          QPathR qa a b → QPathR qa b c → QPathR qa a c
qtransR qa (qnil refl) q' = q'
qtransR qa (qstep c s p) q' = qstep c s (qtransR qa p q')

qsymR : ∀ {A : Set} (qa : QAnalysis A) {a b : A} →
        QPathR qa a b → QPathR qa b a
qsymR qa (qnil refl) = qnil refl
qsymR qa (qstep c s p) =
  qtransR qa (qsymR qa p) (share→path qa (QAnalysis.share-sym qa s))

--------------------------------------------------------------------------------
-- §4. 实例：AtkinQ1 边连通（复用 Topology/AtkinQ1.agda）
--------------------------------------------------------------------------------

open import Sovereign.Topology.AtkinQ1
  using (Edge; Edge-share; share-sym)
  renaming (e01 to at-e01; e12 to at-e12)

atkin-q1 : QAnalysis Edge
atkin-q1 = record { Shared = Edge-share ; share-sym = share-sym }

atkin-q1-refl-check : QPathR atkin-q1 at-e01 at-e01
atkin-q1-refl-check = qreflR atkin-q1 at-e01

atkin-q1-share→path : Edge-share at-e01 at-e12 → QPathR atkin-q1 at-e01 at-e12
atkin-q1-share→path = share→path atkin-q1

atkin-q1-trans-check :
  QPathR atkin-q1 at-e01 at-e12 → QPathR atkin-q1 at-e12 at-e01 →
  QPathR atkin-q1 at-e01 at-e01
atkin-q1-trans-check p q = qtransR atkin-q1 p q
