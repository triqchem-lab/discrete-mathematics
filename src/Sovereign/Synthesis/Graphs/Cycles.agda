{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Synthesis.Graphs.Cycles
-- 圈、圈空间雏形与 Euler 回路
--
-- 数学背景：圈 = 无重复顶点的闭途径（长 ≥2 内部顶点——Trees.Cycle 口径）；
--   圈空间 = 圈的边支撑在对称差下（雏形：载体 + 支撑 + 对称差谓词——群律立界）；
--   Euler 回路 = 经过每条边的闭链（判据「连通 + 全顶点偶度」为经典定理——立界注记，
--   K3 实例全证）；Hamiltonian 回路为深件（NP 完全面）立界注记。
--
-- 核心原则：
-- 1. 圈口径与 Trees.Cycle 一致（闭链 + NoDup + 长度下界）——零重证
-- 2. C3（三角形）为标准实例全证：圈见证 + Euler 回路
-- 3. 圈空间只立雏形（carrier/support/symdiff）——群律不硬拱
-- 4. 判据类定理（Euler/Hamiltonian）如实立界
--
-- 包含：clen · EdgeOf · EulerCircuit · CycleSpace 雏形 · C3/K3 实例
--       · c3-cycle / euler-K3 · 核对层

module Sovereign.Synthesis.Graphs.Cycles where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

open import Sovereign.Synthesis.Graphs.GraphBasic using (Graph; V; adj; adj-sym; adj-irrefl)
open import Sovereign.Synthesis.Graphs.Connectivity using (Reachable; reflR; stepR; Connected)
open import Sovereign.Synthesis.Graphs.Trees
  using (Chain; chn; chs; _∈ᵥ_; ev-here; ev-there; NoDup; nd-[]; nd-∷; Cycle)

------------------------------------------------------------------------
-- 基础件层：边支撑 / 圈长
------------------------------------------------------------------------

-- 边（有序对——对称性由 adj-sym 承载，支撑按有序对记录）
EdgeOf : (G : Graph) {x y : V G} {vs : List (V G)}
       → Chain G x y vs → List (V G × V G)
EdgeOf G (chn x) = []
EdgeOf G (chs {x = x} {y = y} h c) = (x , y) ∷ EdgeOf G c

-- 圈长（内部顶点数）
clen : {G : Graph} {x : V G} (vs : List (V G)) → Cycle G x vs → ℕ
clen vs _ = length vs

------------------------------------------------------------------------
-- Euler 回路（覆盖形——「恰一次」性立界注记）
------------------------------------------------------------------------

-- c 是 x 处 Euler 候选：闭链 + 每条有向邻接边出现在支撑（正/反向择一）
EulerCircuit : (G : Graph) (x : V G) (vs : List (V G)) → Set
EulerCircuit G x vs =
  Σ (Chain G x x vs) λ c
    → (∀ (a b : V G) → adj G a b
       → ((a , b) ∈ᵥ EdgeOf G c) ⊎ ((b , a) ∈ᵥ EdgeOf G c))

------------------------------------------------------------------------
-- 圈空间雏形
------------------------------------------------------------------------

-- 雏形：边支撑在对称差下的交换群结构（群律/单位元/逆元=自反——立界注记）
record CycleSpace (G : Graph) : Set₁ where
  field
    carrier : Set                        -- 圈的边支撑（抽象载体）
    symdiff : carrier → carrier → carrier
    contains : V G × V G → carrier → Set -- 边隶属支撑
  -- 立界：(carrier, symdiff, ∅) 交换群律 + 圈支撑对 symdiff 封闭

------------------------------------------------------------------------
-- 实例层：Tri / K3（C3 圈 + Euler 回路——全证）
------------------------------------------------------------------------

data Tri : Set where
  t0 t1 t2 : Tri

neq-t01 : t0 ≡ t1 → ⊥
neq-t01 ()

neq-t02 : t0 ≡ t2 → ⊥
neq-t02 ()

neq-t10 : t1 ≡ t0 → ⊥
neq-t10 ()

neq-t12 : t1 ≡ t2 → ⊥
neq-t12 ()

neq-t20 : t2 ≡ t0 → ⊥
neq-t20 ()

neq-t21 : t2 ≡ t1 → ⊥
neq-t21 ()

adj3 : Tri → Tri → Set
adj3 x y = x ≡ y → ⊥

adj3-sym : ∀ {x y} → adj3 x y → adj3 y x
adj3-sym f e = f (sym e)

adj3-irrefl : ∀ {x} → adj3 x x → ⊥
adj3-irrefl f = f refl

K3 : Graph
K3 = record
  { V          = Tri
  ; adj        = adj3
  ; adj-sym    = adj3-sym
  ; adj-irrefl = adj3-irrefl
  }

-- C3 开口途径：t0→t1→t2（终点 = 末内部顶点 t2——Chain 语义）
c3-chain : Chain K3 t0 t2 (t1 ∷ t2 ∷ [])
c3-chain = chs neq-t01 (chs neq-t12 (chn t2))

-- C3 闭链（Euler 用）：t0→t1→t2→t0（vs 含回顶点）
c3-closed : Chain K3 t0 t0 (t1 ∷ t2 ∷ t0 ∷ [])
c3-closed = chs neq-t01 (chs neq-t12 (chs neq-t20 (chn t0)))

-- NoDup (t0∷t1∷t2∷[]) ——三构造子互异（模式不合一直消解）
not-in-0 : t0 ∈ᵥ (t1 ∷ t2 ∷ []) → ⊥
not-in-0 (ev-there (ev-there ()))

not-in-1 : t1 ∈ᵥ (t2 ∷ []) → ⊥
not-in-1 (ev-there ())

not-in-2 : t2 ∈ᵥ [] → ⊥
not-in-2 ()

c3-nodup : NoDup (t0 ∷ t1 ∷ t2 ∷ [])
c3-nodup = nd-∷ not-in-0 (nd-∷ not-in-1 (nd-∷ not-in-2 nd-[]))

c3-len : 2 ≤ length (t1 ∷ t2 ∷ [])
c3-len = s≤s (s≤s z≤n)

c3-cycle : Cycle K3 t0 (t1 ∷ t2 ∷ [])
c3-cycle = t2 , c3-chain , neq-t20 , c3-nodup , c3-len

-- K3 的 Euler 回路（覆盖形——6 个有序邻接边逐案）
euler-covers-K3 : ∀ (a b : Tri) → adj3 a b
                → ((a , b) ∈ᵥ EdgeOf K3 c3-closed)
                 ⊎ ((b , a) ∈ᵥ EdgeOf K3 c3-closed)
euler-covers-K3 t0 t1 h = inj₁ ev-here
euler-covers-K3 t0 t2 h = inj₂ (ev-there (ev-there ev-here))
euler-covers-K3 t1 t0 h = inj₂ ev-here
euler-covers-K3 t1 t2 h = inj₁ (ev-there ev-here)
euler-covers-K3 t2 t0 h = inj₁ (ev-there (ev-there ev-here))
euler-covers-K3 t2 t1 h = inj₂ (ev-there ev-here)
euler-covers-K3 t0 t0 h = ⊥-elim (h refl)
euler-covers-K3 t1 t1 h = ⊥-elim (h refl)
euler-covers-K3 t2 t2 h = ⊥-elim (h refl)

euler-K3 : EulerCircuit K3 t0 (t1 ∷ t2 ∷ t0 ∷ [])
euler-K3 = c3-closed , euler-covers-K3

------------------------------------------------------------------------
-- 核对层
------------------------------------------------------------------------

check-c3-cycle : Cycle K3 t0 (t1 ∷ t2 ∷ [])
check-c3-cycle = c3-cycle

check-euler-K3 : EulerCircuit K3 t0 (t1 ∷ t2 ∷ t0 ∷ [])
check-euler-K3 = euler-K3

-- C3 支撑三边（c3-chain 边表 = (t0,t1)∷(t1,t2)∷(t2,t0)∷[]——defeq 形）
check-edges-c3 : EdgeOf K3 c3-closed ≡ ((t0 , t1) ∷ (t1 , t2) ∷ (t2 , t0) ∷ [])
check-edges-c3 = refl

-- 立界注记（诚实边界）：
--   (i) 「恰一次」Euler 性（支撑恰一次——NoDup (EdgeOf c) 形）+ 判据定理
--       （连通 + 偶度 ⟺ Euler 回路存在——经典定理 ~300+ 行，深件立界）
--   (ii) 圈空间群律（symdiff 交换群 + 圈支撑封闭——~80-120 行）
--   (iii) Hamiltonian 回路（NP 完全判据面——深件诚实界，不做一般形）
--   (iv) 圈空间与同调衔接（Trees.Cycle ↔ 边界算子 kernel——Hodge 线桥接注记）
