{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.Matchings
-- 任务池 P2 图论续第一件：图匹配——选定边集两两不交（每顶点至多一条选定边）。
--   数学背景：匹配/最大匹配/完美匹配是组合优化基础面；Hall 定理（完美匹配的
--   邻域刻画）与 König 定理是经典深件——本模块定义层 + 小例全证 + 深件立界。
--
-- 核心原则：
-- 1. 关系入定义（Matching record：picked 关系 + is-edge/symm/disjoint 结构公理；
--    「两两不交」由 disjoint + symm 承载——presentation 最小性自检过）
-- 2. 小例全证（K2 完美匹配/极大性；K3 完美匹配不存在/单边极大）+ 一般形立界
-- 3. 0 postulate / 0 hole；复用零重证（Graph 面 GraphBasic；K2 件 Trees 直引）
--
-- 包含：Matching · covers/Unmatched/Perfect/Maximal · K2/K3 实例（全证）· 核对层

module Sovereign.Topology.Graphs.Matchings where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Sovereign.Topology.Graphs.GraphBasic using (Graph; V; adj; adj-sym; adj-irrefl)
open import Sovereign.Topology.Graphs.Trees using (Bit; b0; b1; neq01; neq10; adj2; adj2-sym; adj2-irrefl; y-flip; K2)

--------------------------------------------------------------------------------
-- §1 定义层：Matching（关系入定义）
--------------------------------------------------------------------------------

-- 匹配 = 选定边关系 picked + 三公理：是图边、无向形、每顶点至多一条选定边。
-- ⚠ 最小性自检：is-edge/symm/disjoint = 「匹配」定义的结构公理；
--   导出性质（两两不交的一般形、边数界）不入字段。
record Matching (G : Graph) : Set₁ where
  field
    picked   : V G → V G → Set
    is-edge  : ∀ {x y} → picked x y → adj G x y
    symm     : ∀ {x y} → picked x y → picked y x
    disjoint : ∀ {x y z} → picked x y → picked x z → y ≡ z

open Matching public

-- 覆盖 / 未覆盖 / 完美 / 极大（导出定义——非 record 字段）
covers : (G : Graph) (M : Matching G) → V G → Set
covers G M x = Σ (V G) (λ y → picked M x y)

Unmatched : (G : Graph) (M : Matching G) → V G → Set
Unmatched G M x = covers G M x → ⊥

-- 完美匹配：每顶点被某条选定边覆盖
Perfect : (G : Graph) (M : Matching G) → Set
Perfect G M = ∀ x → covers G M x

-- 极大匹配：无「两端均未覆盖」的边可加（augmentable 的否定形）
Maximal : (G : Graph) (M : Matching G) → Set
Maximal G M =
  ∀ x y → adj G x y → Unmatched G M x → Unmatched G M y → ⊥

--------------------------------------------------------------------------------
-- §2 主引理层：K2 全证（完美 + 极大）
--------------------------------------------------------------------------------

-- K2 上选中唯一边即完美匹配（picked = adj2 本身——一图一边）
mK2 : Matching K2
mK2 = record
  { picked   = adj2
  ; is-edge  = λ h → h
  ; symm     = adj2-sym
  ; disjoint = λ h1 h2 → trans (y-flip _ _ h1) (sym (y-flip _ _ h2))
  }

-- 完美：两顶点各被唯一边覆盖（B 顶点证 —— refl 级数据）
cover-b0 : covers K2 mK2 b0
cover-b0 = b1 , neq01

cover-b1 : covers K2 mK2 b1
cover-b1 = b0 , neq10

perfect-K2 : Perfect K2 mK2
perfect-K2 b0 = cover-b0
perfect-K2 b1 = cover-b1

-- 极大：两顶点全覆盖 ⇒ 无未覆盖对可加
maximal-K2 : Maximal K2 mK2
maximal-K2 b0 b1 h u0 _ = u0 cover-b0
maximal-K2 b1 b0 h _ u1 = u1 cover-b0
maximal-K2 b0 b0 h _ _ = ⊥-elim (h refl)
maximal-K2 b1 b1 h _ _ = ⊥-elim (h refl)

--------------------------------------------------------------------------------
-- §3 主引理层：K3 全证（完美匹配不存在 + 单边极大）
--------------------------------------------------------------------------------

-- 三顶点完全图（adj3 = 不同——Trees K2 同款形）
data Tri : Set where
  t0 t1 t2 : Tri

adj3 : Tri → Tri → Set
adj3 x y = x ≡ y → ⊥

adj3-sym : ∀ {x y} → adj3 x y → adj3 y x
adj3-sym f e = f (sym e)

adj3-irrefl : ∀ {x} → adj3 x x → ⊥
adj3-irrefl f = f refl

t0≢t1 : t0 ≡ t1 → ⊥
t0≢t1 ()

t0≢t2 : t0 ≡ t2 → ⊥
t0≢t2 ()

t1≢t2 : t1 ≡ t2 → ⊥
t1≢t2 ()

t1≢t0 : t1 ≡ t0 → ⊥
t1≢t0 ()

K3 : Graph
K3 = record
  { V          = Tri
  ; adj        = adj3
  ; adj-sym    = adj3-sym
  ; adj-irrefl = adj3-irrefl
  }

-- 顶点三歧：is-edge ⟹ 第二顶点不同（k3-neq 型消解）
k3-y-neq : ∀ {x y} → adj3 x y → x ≡ y → ⊥
k3-y-neq f e = f e

-- 完美匹配不存在：t0 被某边覆盖后，剩余两点的覆盖必与 disjoint 冲突
perfect-K3-imp-false : (M : Matching K3) → Perfect K3 M → ⊥
perfect-K3-imp-false M perf = go (perf t0)
  where
  go : covers K3 M t0 → ⊥
  go (t0 , p) = adj3-irrefl (is-edge M p)
  go (t1 , p01) = go2 (perf t2)
    where
    go2 : covers K3 M t2 → ⊥
    go2 (t0 , p20) = t1≢t2 (disjoint M p01 (symm M p20))
    go2 (t1 , p21) = t0≢t2 (disjoint M (symm M p01) (symm M p21))
    go2 (t2 , p22) = adj3-irrefl (is-edge M p22)
  go (t2 , p02) = go3 (perf t1)
    where
    go3 : covers K3 M t1 → ⊥
    go3 (t0 , p10) = t1≢t2 (sym (disjoint M p02 (symm M p10)))
    go3 (t1 , p11) = adj3-irrefl (is-edge M p11)
    go3 (t2 , p12) = t1≢t0 (disjoint M (symm M p12) (symm M p02))

-- 单边匹配（t0-t1）：极大（唯一未覆盖点 t2 的所有邻点均被覆盖）
mK3 : Matching K3
mK3 = record
  { picked   = λ x y → (x ≡ t0 × y ≡ t1) ⊎ (x ≡ t1 × y ≡ t0)
  ; is-edge  = λ { {x} {y} p → λ e → m3-edge p e }
  ; symm     = λ { {x} {y} p → m3-symm p }
  ; disjoint = λ { {x} {y} {z} p q → m3-disj p q }
  }
  where
  m3-edge : ∀ {x y} → ((x ≡ t0 × y ≡ t1) ⊎ (x ≡ t1 × y ≡ t0)) → x ≡ y → ⊥
  m3-edge (inj₁ (e0 , e1)) e = t0≢t1 (trans (sym e0) (trans e e1))
  m3-edge (inj₂ (e1 , e0)) e = t1≢t0 (trans (sym e1) (trans e e0))
  m3-symm : ∀ {x y} → ((x ≡ t0 × y ≡ t1) ⊎ (x ≡ t1 × y ≡ t0)) → ((y ≡ t0 × x ≡ t1) ⊎ (y ≡ t1 × x ≡ t0))
  m3-symm (inj₁ (e0 , e1)) = inj₂ (e1 , e0)
  m3-symm (inj₂ (e1 , e0)) = inj₁ (e0 , e1)
  m3-disj : ∀ {x y z} → ((x ≡ t0 × y ≡ t1) ⊎ (x ≡ t1 × y ≡ t0))
          → ((x ≡ t0 × z ≡ t1) ⊎ (x ≡ t1 × z ≡ t0)) → y ≡ z
  m3-disj (inj₁ (_ , e1)) (inj₁ (_ , f1)) = trans e1 (sym f1)
  m3-disj (inj₂ (_ , e0)) (inj₂ (_ , f0)) = trans e0 (sym f0)
  m3-disj (inj₁ (e0 , _)) (inj₂ (f1' , _)) = ⊥-elim (t0≢t1 (trans (sym e0) f1'))
  m3-disj (inj₂ (e1 , _)) (inj₁ (f0' , _)) = ⊥-elim (t0≢t1 (trans (sym f0') e1))

maximal-K3 : Maximal K3 mK3
maximal-K3 t2 t0 h u2 u0 = u0 (t1 , inj₁ (refl , refl))
maximal-K3 t2 t1 h u2 u1 = u1 (t0 , inj₂ (refl , refl))
maximal-K3 t0 t0 h _ _ = ⊥-elim (h refl)
maximal-K3 t1 t1 h _ _ = ⊥-elim (h refl)
maximal-K3 t2 t2 h _ _ = ⊥-elim (h refl)
maximal-K3 t0 t2 h u0 _ = u0 (t1 , inj₁ (refl , refl))
maximal-K3 t1 t2 h u1 _ = u1 (t0 , inj₂ (refl , refl))
maximal-K3 t0 t1 h u0 _ = u0 (t1 , inj₁ (refl , refl))
maximal-K3 t1 t0 h u1 _ = u1 (t0 , inj₂ (refl , refl))

--------------------------------------------------------------------------------
-- §4 核对层
--------------------------------------------------------------------------------

check-cover-K2 : covers K2 mK2 b0
check-cover-K2 = cover-b0

check-perfect-K2 : Perfect K2 mK2
check-perfect-K2 = perfect-K2

check-K3-not-perfect : (M : Matching K3) → Perfect K3 M → ⊥
check-K3-not-perfect = perfect-K3-imp-false

-- 立界注记（§5——深件不硬拱）：
-- (i) Hall 定理（完美匹配的邻域刻画——经典深件）；
-- (ii) 最大匹配 = 极大匹配的基数最大形（算法面）；
-- (iii) König 定理（二分图最大匹配=最小点覆盖）；
-- (iv) 一般图 matching 多项式/匹配族计数。
