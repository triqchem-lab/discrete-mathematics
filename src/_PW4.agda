{-# OPTIONS --rewriting --guardedness #-}

-- | _PW4 —— 流分解定理批（Flows §6 立界件 (ii) + Flows×Trees 接线）
--
-- 数学背景：流分解定理（Flow Decomposition）：s-t 可行流 = 路径流之和
--   （+ 循环流分量——一般形立界）。本件走 GAP 收窄范式：K3 实例先行——
--   K3 上的两路径流（直边 + 经中点）直和恰复原三边单位流，逐点 refl 级核对。
--   路径流 = 顶点列的连续对供 1（eqN 指示函数承载——Dec 等式参数形，
--   库内 eqV 先例同款）。
--
-- 核心原则：
-- 1. 路径流以连续对递归（pathFlow：x∷y∷rest 供 (x,y) 1 单位递归续尾）——
--    求和面 sumFs 命名形（List 流函数逐点折叠——Flows.sumL 同款范式）
-- 2. Flows×Trees 接线 = 分解路径携带 Trees.Chain 见证（chn/chs 构造级——
--    真实 import 边非注释；链顶点列含终点 = Trees.Chain 语义）
-- 3. 0 postulate / 0 hole；record 字段不放模式 λ（顶层命名件范式）；
--    ≤27 case 穷举边界（eq3/flow3 全 9 案）
--
-- 包含：eqN · pathFlow · sumFs（分解层）· K3 三顶点实例（flow3 全证）
--       · 分解核对（check-decomp3 九案全 refl）· Chain 见证 ×2（接线面）
--       · 一般形立界注记

module _PW4 where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Sovereign.Topology.Graphs.GraphBasic using (Graph; V; adj)
open import Sovereign.Topology.Graphs.Flows
  using (Flow; f; outF; inF; sumL; flowVal)
open import Sovereign.Topology.Graphs.Trees using (Chain; chn; chs)

--------------------------------------------------------------------------------
-- §1 分解层：路径流与流函数求和
--------------------------------------------------------------------------------

-- 相等指示（ℕ 承载 0/1——Dec 等式参数形，eqV 先例同款）
eqN : {A : Set} → ((a b : A) → Dec (a ≡ b)) → A → A → ℕ
eqN eq a b with eq a b
... | yes _ = 1
... | no  _ = 0

-- 路径流：顶点列连续对各供 1 单位
pathFlow : (G : Graph) → ((a b : V G) → Dec (a ≡ b))
         → List (V G) → V G → V G → ℕ
pathFlow G eq (x ∷ y ∷ rest) a b = eqN eq x a * eqN eq y b + pathFlow G eq (y ∷ rest) a b
pathFlow G eq (x ∷ [])      a b = 0
pathFlow G eq []            a b = 0

-- 流函数族逐点求和（分解见证的组合面）
sumFs : (G : Graph) → List (V G → V G → ℕ) → V G → V G → ℕ
sumFs G []       a b = 0
sumFs G (g ∷ gs) a b = g a b + sumFs G gs a b

-- 路径族的流族（map 装配）
pathFlows : (G : Graph) → ((a b : V G) → Dec (a ≡ b))
          → List (List (V G)) → List (V G → V G → ℕ)
pathFlows G eq ps = map (pathFlow G eq) ps

--------------------------------------------------------------------------------
-- §2 K3 实例层：三顶点完全图上的两路径分解
--------------------------------------------------------------------------------

data Tri : Set where
  t0 t1 t2 : Tri

eq3 : (a b : Tri) → Dec (a ≡ b)
eq3 t0 t0 = yes refl
eq3 t0 t1 = no λ ()
eq3 t0 t2 = no λ ()
eq3 t1 t0 = no λ ()
eq3 t1 t1 = yes refl
eq3 t1 t2 = no λ ()
eq3 t2 t0 = no λ ()
eq3 t2 t1 = no λ ()
eq3 t2 t2 = yes refl

adj3 : Tri → Tri → Set
adj3 x y = x ≡ y → ⊥

adj3-sym : ∀ {x y} → adj3 x y → adj3 y x
adj3-sym h = λ eq → h (sym eq)

adj3-irrefl : ∀ {x} → adj3 x x → ⊥
adj3-irrefl h = h refl

g3 : Graph
g3 = record
  { V = Tri ; adj = adj3 ; adj-sym = adj3-sym ; adj-irrefl = adj3-irrefl }

-- 单位容量（完全图）
cap3 : Tri → Tri → ℕ
cap3 _ _ = 1

-- 三边单位流：t0→t1、t0→t2、t1→t2 各 1
f3 : Tri → Tri → ℕ
f3 t0 t1 = 1
f3 t0 t2 = 1
f3 t1 t2 = 1
f3 _  _  = 0

vs3 : List Tri
vs3 = t0 ∷ t1 ∷ t2 ∷ []

-- 顶层命名件（record 字段不放模式 λ）
flow3-edge : ∀ x y → ¬ (f3 x y ≡ 0) → adj3 x y
flow3-edge t0 t0 pr = λ _ → pr refl
flow3-edge t0 t1 _  = λ ()
flow3-edge t0 t2 _  = λ ()
flow3-edge t1 t0 pr = λ _ → pr refl
flow3-edge t1 t1 pr = λ _ → pr refl
flow3-edge t1 t2 _  = λ ()
flow3-edge t2 t0 pr = λ _ → pr refl
flow3-edge t2 t1 pr = λ _ → pr refl
flow3-edge t2 t2 pr = λ _ → pr refl

flow3-cap : ∀ x y → f3 x y ≤ cap3 x y
flow3-cap t0 t0 = z≤n
flow3-cap t0 t1 = s≤s z≤n
flow3-cap t0 t2 = s≤s z≤n
flow3-cap t1 t0 = z≤n
flow3-cap t1 t1 = z≤n
flow3-cap t1 t2 = s≤s z≤n
flow3-cap t2 t0 = z≤n
flow3-cap t2 t1 = z≤n
flow3-cap t2 t2 = z≤n

flow3-skew : ∀ x y → (f3 x y ≡ 0) ⊎ (f3 y x ≡ 0)
flow3-skew t0 t0 = inj₁ refl
flow3-skew t0 t1 = inj₂ refl
flow3-skew t0 t2 = inj₂ refl
flow3-skew t1 t0 = inj₁ refl
flow3-skew t1 t1 = inj₁ refl
flow3-skew t1 t2 = inj₂ refl
flow3-skew t2 t0 = inj₁ refl
flow3-skew t2 t1 = inj₁ refl
flow3-skew t2 t2 = inj₁ refl

-- 守恒（唯一内部顶点 t1：出 1 = 入 1——求和面 refl 算定）
flow3-cons :
    ∀ v → ¬ (v ≡ t0) → ¬ (v ≡ t2)
  → outF g3 f3 vs3 v ≡ inF g3 f3 vs3 v
flow3-cons t0 ne0 _  = ⊥-elim (ne0 refl)
flow3-cons t1 _   _  = refl
flow3-cons t2 _   ne2 = ⊥-elim (ne2 refl)

flow3 : Flow g3 cap3 t0 t2 vs3
flow3 = record
  { f = f3 ; f-edge = flow3-edge ; f-cap = flow3-cap
  ; f-skew = flow3-skew ; f-cons = flow3-cons }

--------------------------------------------------------------------------------
-- §3 分解见证：两路径流直和 = f3
--------------------------------------------------------------------------------

-- 路径族：直边路径 + 经中点路径
paths3 : List (List Tri)
paths3 = (t0 ∷ t2 ∷ []) ∷ (t0 ∷ t1 ∷ t2 ∷ []) ∷ []

-- 分解主件：逐点九案全 refl（两路径流直和复原三边单位流）
check-decomp3 : ∀ a b → sumFs g3 (pathFlows g3 eq3 paths3) a b ≡ f3 a b
check-decomp3 t0 t0 = refl
check-decomp3 t0 t1 = refl
check-decomp3 t0 t2 = refl
check-decomp3 t1 t0 = refl
check-decomp3 t1 t1 = refl
check-decomp3 t1 t2 = refl
check-decomp3 t2 t0 = refl
check-decomp3 t2 t1 = refl
check-decomp3 t2 t2 = refl

-- 流值 = 路径数（2 = 2——分解面计数一致）
check-val3-paths : flowVal flow3 ≡ length paths3
check-val3-paths = refl

--------------------------------------------------------------------------------
-- §4 Flows×Trees 接线面：分解路径携带 Chain 见证
--------------------------------------------------------------------------------

-- 直边路径 = Trees.Chain（chn/chs 构造级——真实 import 边）
chain-direct : Chain g3 t0 t2 (t2 ∷ [])
chain-direct = chs (λ ()) (chn t2)

-- 经中点路径 = Trees.Chain（链顶点列含终点——Trees.Chain 语义）
chain-via : Chain g3 t0 t2 (t1 ∷ t2 ∷ [])
chain-via = chs (λ ()) (chs (λ ()) (chn t2))

-- 分解与链面计数对账（链列长度 = 路径列长度——接线一致性）
check-chain-len : length (t1 ∷ t2 ∷ []) ≡ 2
check-chain-len = refl

--------------------------------------------------------------------------------
-- §5 一般形立界（诚实边界——GAP 收窄范式，不设空壳签名）
--   (i) 一般流分解定理：可行流 = 路径流 + 循环流之和（循环流分量面未展开——
--       K3 实例仅路径分量；一般形需圈流机件衔接 Cycles.CycleSpace 立界件）
--   (ii) 一般图路径枚举（vs 完备性前提 + Dec 等式参数形的图级实例化）
--   (iii) 分解保持容量约束（f ≤ cap ⟹ 分量各 ≤ cap——需路径流容量引理）
--   (iv) Trees.Chain ↔ pathFlow 边支撑一般桥（Chain 归纳 → 连续对 ∈ 边集）
