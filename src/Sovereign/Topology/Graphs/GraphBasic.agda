{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.GraphBasic
-- 无向简单图基础（Mathlib Combinatorics.SimpleGraph 对标）
--
-- 数学背景：简单图 = 顶点集 + 对称且无自环的邻接关系（SimpleGraph 语义）。
--   与 BarceloAHomotopy.DiGraph（有向图）互导：对称无自环的有向图 ⟺ 简单图。
--   本模块是任务池 T-2 批第一件（缺面清单 §四 GraphBasic 原子分解五件）。
--
-- 核心原则：
-- 1. 关系入定义（Graph record：adj + 对称 + 无自环 = 结构公理，presentation 最小性；
--    导出性质（可达/同构传递等）一律降定理不入字段）
-- 2. 复用零重证（BarceloAHomotopy 的 DiGraph/Walk 只 import；Foundation.Equiv 的
--    to/from+往返范式迁移到 GraphIso）
-- 3. 0 postulate / 0 hole；穷举边界纪律（Bool/Fin 小例 ≤27 case）
--
-- 包含：Graph（对称形）· toDiGraph/fromDiGraph 互导往返 · 邻接/度（枚举参数形）
--       · GraphIso（≅ 双向件）· subGraph/removeV/removeEdge · 诱导商图（商无关形）· 核对层

module Sovereign.Topology.Graphs.GraphBasic where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Sovereign.Topology.BarceloAHomotopy as BA

--------------------------------------------------------------------------------
-- §1 基础件层：Graph 定义（关系入定义——对称 + 无自环 = 简单图的结构公理）
--------------------------------------------------------------------------------

-- 简单图：顶点集 V、邻接 adj、对称性 adj-sym、无自环 adj-irrefl。
-- ⚠ 三字段分类自检（presentation 最小性判据）：
--   adj = 载体关系；adj-sym/adj-irrefl = 「简单图」定义的结构公理（同 Group 定律字段
--   的合法性）；导出性质（如度和为偶）不入字段。
record Graph : Set₁ where
  field
    V         : Set
    adj       : V → V → Set
    adj-sym   : ∀ {x y} → adj x y → adj y x
    adj-irrefl : ∀ {x} → adj x x → ⊥

-- 投影开面（record 字段的非限定访问——V/adj/adj-sym/adj-irrefl）
open Graph public

-- 邻接谓词别名（读面友好）
Adj : (G : Graph) → V G → V G → Set
Adj G = adj G

--------------------------------------------------------------------------------
-- §2 主引理层：DiGraph 互导（BarceloAHomotopy.DiGraph ⇄ Graph）
--------------------------------------------------------------------------------

-- 有向 → 简单：抹去方向（对称无自环前提显式携带）
fromDiGraph :
    (D : BA.DiGraph)
  → (symD : ∀ {x y} → BA.DiGraph.edge D x y → BA.DiGraph.edge D y x)
  → (irrD : ∀ {x} → BA.DiGraph.edge D x x → ⊥)
  → Graph
fromDiGraph D symD irrD = record
  { V          = BA.DiGraph.V D
  ; adj        = BA.DiGraph.edge D
  ; adj-sym    = symD
  ; adj-irrefl = irrD
  }

-- 简单 → 有向：对称关系可安全看作有向边集
toDiGraph : Graph → BA.DiGraph
toDiGraph G = record { V = V G ; edge = adj G }

-- 互导往返（record η 承载——两向 definitional）
roundtrip-dig :
    (D : BA.DiGraph)
  → (symD : ∀ {x y} → BA.DiGraph.edge D x y → BA.DiGraph.edge D y x)
  → (irrD : ∀ {x} → BA.DiGraph.edge D x x → ⊥)
  → toDiGraph (fromDiGraph D symD irrD) ≡ D
roundtrip-dig D symD irrD = refl

roundtrip-graph :
    (G : Graph)
  → fromDiGraph (toDiGraph G) (adj-sym G) (adj-irrefl G) ≡ G
roundtrip-graph G = refl

--------------------------------------------------------------------------------
-- §3 主引理层：邻接与度（枚举参数形——度 = 枚举面上的邻接计数）
--------------------------------------------------------------------------------

-- 度的计数形：沿枚举列表数邻接顶点。
-- 语义注记：degree G dec enum x = 「enum 中与 x 邻接的顶点个数」——
--   enum 覆盖全部顶点时即为真度数（完全枚举假设在调用侧声明，本件不重证）。
count-adj :
    (G : Graph)
  → (dec : ∀ x y → Dec (adj G x y))
  → (enum : List (V G))
  → (x : V G)
  → ℕ
count-adj G dec [] x = zero
count-adj G dec (y ∷ ys) x with dec y x
... | yes _ = suc (count-adj G dec ys x)
... | no  _ = count-adj G dec ys x

degree :
    (G : Graph)
  → (dec : ∀ x y → Dec (adj G x y))
  → (enum : List (V G))
  → (x : V G)
  → ℕ
degree G dec enum x = count-adj G dec enum x

-- 孤立点（导出性质——不入 record 字段）
isIsolated : (G : Graph) → V G → Set
isIsolated G x = ∀ y → adj G x y → ⊥

--------------------------------------------------------------------------------
-- §4 主引理层：GraphIso（Foundation.Equiv 的 to/from+往返范式迁移）
--------------------------------------------------------------------------------

record GraphIso (G H : Graph) : Set₁ where
  field
    toV      : V G → V H
    fromV    : V H → V G
    toV-adj  : ∀ {x y} → adj G x y → adj H (toV x) (toV y)
    fromV-adj : ∀ {x y} → adj H x y → adj G (fromV x) (fromV y)
    to-from  : ∀ y → toV (fromV y) ≡ y
    from-to  : ∀ x → fromV (toV x) ≡ x

infix 4 _≅ᵍ_
_≅ᵍ_ : Graph → Graph → Set₁
_≅ᵍ_ = GraphIso

-- 恒等同构（导出件）
iso-refl : (G : Graph) → GraphIso G G
iso-refl G = record
  { toV = λ x → x
  ; fromV = λ x → x
  ; toV-adj = λ h → h
  ; fromV-adj = λ h → h
  ; to-from = λ y → refl
  ; from-to = λ x → refl
  }

-- 同构对称（导出件——交换 to/from 即可）
iso-sym : {G H : Graph} → GraphIso G H → GraphIso H G
iso-sym i = record
  { toV = GraphIso.fromV i
  ; fromV = GraphIso.toV i
  ; toV-adj = GraphIso.fromV-adj i
  ; fromV-adj = GraphIso.toV-adj i
  ; to-from = GraphIso.from-to i
  ; from-to = GraphIso.to-from i
  }

--------------------------------------------------------------------------------
-- §5 主引理层：子图 / 删点 / 删边 / 诱导商图（商无关形）
--------------------------------------------------------------------------------

-- 诱导子图：顶点子集 W，边继承自 G（对称/无自环保留）
subGraph : (G : Graph) → (W : V G → Set) → Graph
subGraph G W = record
  { V = Σ (V G) W
  ; adj = λ u v → adj G (proj₁ u) (proj₁ v)
  ; adj-sym = λ h → adj-sym G h
  ; adj-irrefl = λ h → adj-irrefl G h
  }

-- 删点 x：顶点集保留、x 处边全断（x 退化为孤立点——割点语义足够）
removeV : (G : Graph) → (x : V G) → Graph
removeV G x = record
  { V = V G
  ; adj = λ y z → adj G y z × (y ≡ x → ⊥) × (z ≡ x → ⊥)
  ; adj-sym = λ { (h , ny , nz) → adj-sym G h , nz , ny }
  ; adj-irrefl = λ { (h , _ , _) → adj-irrefl G h }
  }

-- 对调配对（顶层具名件——泛型载体免命名捕获；免匹配范式）
flip-edge-pair :
    {U : Set} {u v x y : U}
  → (v ≡ x × u ≡ y) ⊎ (v ≡ y × u ≡ x)
  → (u ≡ x × v ≡ y) ⊎ (u ≡ y × v ≡ x)
flip-edge-pair (inj₁ (p1 , p2)) = inj₂ (p2 , p1)
flip-edge-pair (inj₂ (p1 , p2)) = inj₁ (p2 , p1)

-- 删边 (x,y)：仅断这一对（含反向）
removeEdge : (G : Graph) → (x y : V G) → Graph
removeEdge G x y = record
  { V = V G
  ; adj = λ u v → adj G u v × ¬ ((u ≡ x × v ≡ y) ⊎ (u ≡ y × v ≡ x))
  ; adj-sym = λ { (h , np) → adj-sym G h , λ p → np (flip-edge-pair p) }
  ; adj-irrefl = λ { (h , _) → adj-irrefl G h }
  }

-- 诱导商图（商无关形）：给定投影 π : V → Q，商邻接 = 像上的边提升。
-- ⚠ 诚实边界：QAdj 保证对称，但商面无自环需要「类间无边」前提（q-irrefl-under）；
--   连通分支商（Connectivity.π₀）中类内有边时商面允许自环——这是数学本性非缺口。
module QuotientGraph (G : Graph) (Q : Set) (π : V G → Q) where

  data QAdj : Q → Q → Set where
    q-adj : ∀ {x y} → adj G x y → QAdj (π x) (π y)

  q-sym : ∀ {a b} → QAdj a b → QAdj b a
  q-sym (q-adj h) = q-adj (adj-sym G h)

  -- 逆像引理（QAdj 消解为提升见证——变量索引形，π 反演免）
  q-edge-inv :
      {a b : Q}
    → QAdj a b
    → Σ (V G) (λ x → Σ (V G) (λ y → (a ≡ π x) × (b ≡ π y) × adj G x y))
  q-edge-inv (q-adj h) = _ , _ , refl , refl , h

  -- 商面无自环的充分条件（类间无边 ⇒ 像点无环）
  -- 形态注记：经 q-edge-inv 逆像 + 显式传输（π 投影非单射不反演——Q 索引统一 stuck 绕开）
  q-irrefl-under :
      (sep : ∀ {x y} → adj G x y → π x ≡ π y → ⊥)
    → ∀ {a} → QAdj a a → ⊥
  q-irrefl-under sep {a} q = go (q-edge-inv q)
    where
    go : Σ (V G) (λ x → Σ (V G) (λ y → (a ≡ π x) × (a ≡ π y) × adj G x y)) → ⊥
    go (x , y , ax , ay , h) = sep h (trans (sym ax) ay)

--------------------------------------------------------------------------------
-- §6 核对层：K2 具体例（Bool 二点全图——refl 级核对）
--------------------------------------------------------------------------------

-- Bool 二点相异关系（具名件——真值表 4 case）
_≟b_ : (x y : Bool) → Dec (x ≡ y)
true ≟b true = yes refl
true ≟b false = no λ ()
false ≟b true = no λ ()
false ≟b false = yes refl

K2 : Graph
K2 = record
  { V = Bool
  ; adj = λ x y → ¬ (x ≡ y)
  ; adj-sym = λ h → λ eq → h (sym eq)
  ; adj-irrefl = λ h → h refl
  }

-- 核对 1：无自环（K2 的 adj x x 为空——空模式收口）
check-K2-irrefl : adj K2 true true → ⊥
check-K2-irrefl h = h refl

-- 核对 2：对称（导出形传递）
check-K2-sym : adj K2 true false → adj K2 false true
check-K2-sym = adj-sym K2

-- 核对 3：度计数（枚举 [true,false]——true 的邻接数 = 1）
decK2 : ∀ x y → Dec (adj K2 x y)
decK2 x y with x ≟b y
... | yes eq = no λ h → h eq
... | no neq = yes neq

check-K2-degree : degree K2 decK2 (true ∷ false ∷ []) true ≡ suc zero
check-K2-degree = refl

-- 核对 4：恒等同构 / 对称传递
check-iso-K2 : GraphIso K2 K2
check-iso-K2 = iso-refl K2

check-iso-sym : GraphIso K2 K2
check-iso-sym = iso-sym (iso-refl K2)

-- 核对 5：互导往返（record η definitional——DiGraph 侧）
check-roundtrip : toDiGraph (fromDiGraph (toDiGraph K2) (adj-sym K2) (adj-irrefl K2))
                    ≡ toDiGraph K2
check-roundtrip = refl
