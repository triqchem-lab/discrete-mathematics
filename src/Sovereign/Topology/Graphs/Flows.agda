{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.Flows
-- 网络流基础（Mathlib Combinatorics.SimpleGraph.Flow 对标）
--
-- 数学背景：有向容量网络上的可行流 = 容量约束 + 反对称 + 内部顶点守恒；
--   割 = 顶点二分（s 侧/t 侧）+ 割容量；最大流最小割等式是该面的主定理（深件立界）。
--   本模块是任务池 P3 批四（缺面清单 §四 Flows 原子分解五件）。
--
-- 核心原则：
-- 1. 关系入定义（Flow record：容量/反对称/守恒 = 结构公理；导出性质（流值分解等）降定理）
-- 2. 守恒的求和面用**枚举参数形**（vs : List (V G)——GraphBasic degree 同款范式，
--    抽象顶点集 V 无法直接 Σ，枚举列表承载是库内既定形）
-- 3. 0 postulate / 0 hole；小例（K2 单位流）全证 ≤27 case；record 字段不放模式 λ
--    （顶层命名件范式——record 内模式 λ 卡投影合一教训预采纳）
--
-- 包含：sumL/outF/inF 求和面 · Flow（流定义层）· flowVal（流值）· Cut/cutCap（割与割容量）
--       · K2 单位流/割实例（全证）· 核对层

module Sovereign.Topology.Graphs.Flows where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; z≤n; s≤s)
open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Sovereign.Topology.Graphs.GraphBasic using (Graph; V; adj)

--------------------------------------------------------------------------------
-- §1 基础件层：求和面（枚举参数形——GraphBasic degree 范式）
--------------------------------------------------------------------------------

-- 列表求和（ℕ 加幺半群折叠）
sumL : List ℕ → ℕ
sumL []       = 0
sumL (x ∷ xs) = x + sumL xs

-- 出流和（对枚举顶点列表的前向求和）
outF : (G : Graph) → (V G → V G → ℕ) → List (V G) → V G → ℕ
outF G f vs x = sumL (map (λ y → f x y) vs)

-- 入流和
inF : (G : Graph) → (V G → V G → ℕ) → List (V G) → V G → ℕ
inF G f vs x = sumL (map (λ y → f y x) vs)

--------------------------------------------------------------------------------
-- §2 主引理层：Flow 流定义层（关系入定义）
--------------------------------------------------------------------------------

-- 可行流（s 源 t 汇，vs = 顶点枚举）：
--   f-edge 边支撑（流量非零处必有边）｜f-cap 容量约束｜f-skew 反对称（无双向正流）
--   ── 三者为「可行流」的结构公理；守恒 f-cons 携带 s/t 例外。
record Flow (G : Graph) (cap : V G → V G → ℕ) (s t : V G) (vs : List (V G)) : Set where
  field
    f     : V G → V G → ℕ
    f-edge : ∀ x y → ¬ (f x y ≡ 0) → adj G x y
    f-cap  : ∀ x y → f x y ≤ cap x y
    f-skew : ∀ x y → (f x y ≡ 0) ⊎ (f y x ≡ 0)
    f-cons : ∀ v → ¬ (v ≡ s) → ¬ (v ≡ t) → outF G f vs v ≡ inF G f vs v

open Flow public

-- 流值（s 处净出流——ℕ 差形）
flowVal :
    {G : Graph} {cap : V G → V G → ℕ} {s t : V G} {vs : List (V G)}
  → Flow G cap s t vs → ℕ
flowVal {G = G} {s = s} {vs = vs} fl = outF G (f fl) vs s ∸ inF G (f fl) vs s

--------------------------------------------------------------------------------
-- §3 组合层：Cut 割与割容量
--------------------------------------------------------------------------------

-- 割（s 侧特征函数形——Bool 承载判定性）
record Cut (G : Graph) (s t : V G) : Set where
  field
    S     : V G → Bool
    s-in  : S s ≡ true
    t-out : S t ≡ false

open Cut public

-- 边贡献选择器（true,false 跨割边贡献容量；余零）
edge-part : Bool → Bool → ℕ → ℕ
edge-part true false c = c
edge-part _    _     _ = 0

-- 二元表求和（vs × vs 上的核）
sumPairs : (G : Graph) → (V G → V G → ℕ) → List (V G) → List (V G) → ℕ
sumPairs G g []       ys = 0
sumPairs G g (x ∷ xs) ys = sumL (map (g x) ys) + sumPairs G g xs ys

-- 割容量（跨割边容量和——枚举参数形）
cutCap :
    {G : Graph} (cap : V G → V G → ℕ) (S : V G → Bool)
  → (vs : List (V G)) → ℕ
cutCap {G = G} cap S vs = sumPairs G (λ x y → edge-part (S x) (S y) (cap x y)) vs vs

--------------------------------------------------------------------------------
-- §4 实例层：K2 单位流（Bit 载体——Trees 机件复用）
--------------------------------------------------------------------------------

-- Bit 顶点（Trees.K2 机件同源形——自含以防跨模块域错配）
data Bit : Set where
  b0 b1 : Bit

-- K2 邻接（相异即邻——adj2 同款形）
adj2 : Bit → Bit → Set
adj2 x y = x ≡ y → ⊥

adj2-sym : ∀ {x y} → adj2 x y → adj2 y x
adj2-sym h = λ eq → h (sym eq)

adj2-irrefl : ∀ {x} → adj2 x x → ⊥
adj2-irrefl h = h refl

-- K2 图
g2 : Graph
g2 = record
  { V = Bit ; adj = adj2 ; adj-sym = adj2-sym ; adj-irrefl = adj2-irrefl }

-- K2 容量（跨边 1）
cap2 : Bit → Bit → ℕ
cap2 b0 b1 = 1
cap2 b1 b0 = 1
cap2 _  _  = 0

-- 单位流（b0→b1 方向 1）
f2 : Bit → Bit → ℕ
f2 b0 b1 = 1
f2 _  _  = 0

vs2 : List Bit
vs2 = b0 ∷ b1 ∷ []

-- 顶层命名件（record 字段不放模式 λ——投影合一教训预采纳）
flow2-edge : ∀ x y → ¬ (f2 x y ≡ 0) → adj2 x y
flow2-edge b0 b0 pr = λ _ → pr refl
flow2-edge b0 b1 _  = λ eq → neq01b eq
  where
  neq01b : b0 ≡ b1 → ⊥
  neq01b ()
flow2-edge b1 b0 pr = λ _ → pr refl
flow2-edge b1 b1 pr = λ _ → pr refl

flow2-cap : ∀ x y → f2 x y ≤ cap2 x y
flow2-cap b0 b0 = z≤n
flow2-cap b0 b1 = s≤s z≤n
flow2-cap b1 b0 = z≤n
flow2-cap b1 b1 = z≤n

flow2-skew : ∀ x y → (f2 x y ≡ 0) ⊎ (f2 y x ≡ 0)
flow2-skew b0 b0 = inj₁ refl
flow2-skew b0 b1 = inj₂ refl
flow2-skew b1 b0 = inj₁ refl
flow2-skew b1 b1 = inj₁ refl

-- 守恒（K2 无内部顶点——双矛盾消解）
flow2-cons :
    ∀ v → ¬ (v ≡ b0) → ¬ (v ≡ b1)
  → outF g2 f2 vs2 v ≡ inF g2 f2 vs2 v
flow2-cons b0 ne0 _  = ⊥-elim (ne0 refl)
flow2-cons b1 _   ne1 = ⊥-elim (ne1 refl)

-- K2 单位流（组装）
flow2 : Flow g2 cap2 b0 b1 vs2
flow2 = record
  { f = f2 ; f-edge = flow2-edge ; f-cap = flow2-cap
  ; f-skew = flow2-skew ; f-cons = flow2-cons }

-- K2 割（S = {b0}）
S2 : Bit → Bool
S2 b0 = true
S2 b1 = false

cut2 : Cut g2 b0 b1
cut2 = record { S = S2 ; s-in = refl ; t-out = refl }

--------------------------------------------------------------------------------
-- §5 核对层（小例全 refl——枚举面算定）
--------------------------------------------------------------------------------

-- 流值 = 1（outF b0 = f b0 b0 + f b0 b1 = 0+1；inF b0 = 0+0）
check-val2 : flowVal flow2 ≡ 1
check-val2 = refl

-- 割容量 = 1（四对贡献：(b0,b1) 跨割 1，余三对 0）
check-cut2 : cutCap {G = g2} cap2 S2 vs2 ≡ 1
check-cut2 = refl

-- 割与流平衡小例（K2 单位流值 = 割容量——最大流最小割等式的实例面）
check-val-eq-cut : flowVal flow2 ≡ cutCap {G = g2} cap2 S2 vs2
check-val-eq-cut = refl

-- 守恒 vacuous 面核对（outF b0 = 1 的展开形钉死）
check-out-b0 : outF g2 f2 vs2 b0 ≡ 1
check-out-b0 = refl

check-in-b0 : inF g2 f2 vs2 b0 ≡ 0
check-in-b0 = refl

--------------------------------------------------------------------------------
-- §6 立界注记（诚实边界——不设空壳签名）
--   (i) 最大流最小割等式（深件——Ford-Fulkerson/增广路，独立批 300+）
--   (ii) 流分解定理（流 = 路径流+圈流之和——需路径/圈机件衔接 Trees/Cycles）
--   (iii) 整数流定理（容量整数 ⟹ 存在整数最大流）
--   (iv) 守恒面一般定理（vs 完备性前提下的求和不变性——依赖枚举完备性立界）
