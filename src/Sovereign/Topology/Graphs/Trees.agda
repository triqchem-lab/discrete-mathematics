{-# OPTIONS --rewriting --guardedness #-}

-- | Sovereign.Topology.Graphs.Trees
-- 树 = 无简单圈的连通图（构造性形式化）
--
-- 数学背景：树的等价刻画族（无圈连通 / |E|=|V|-1 / 叶存在 / 唯一路径）是图论基础面。
--   本模块以「顶点列路径 Chain + 顶点无重复 NoDup + 长度下界」定义简单圈——
--   长度下界（≥2 内部顶点）排除 back-and-forth 二步假圈（K2 上 a→b→a 不是圈）；
--   树 = Connected × Acyclic；生成树 = 同载体 + 边包含的树子图。
--   K2 实例全证（树 / 无圈 / 叶）；一般定理（叶存在性 / 唯一路径 / |E|=|V|-1）立界注记。
--
-- 核心原则：
-- 1. 简单圈三件套：闭链 + 顶点无重复 + 2 ≤ 长度（二步假圈排除）
-- 2. Chain 逐边归纳（关系入定义）；∈ᵥ/NoDup 自含（免 stdlib 版本差）
-- 3. 复用零重证（Graph/Connected 直用 GraphBasic/Connectivity）
-- 4. 小实例全证 + 一般形立界（诚实分阶段不硬拱）
--
-- 包含：Chain · ∈ᵥ/NoDup · Cycle · Acyclic · Tree · SpanningTree · nadj/IsLeaf
--       · Bit/K2 实例（tree-K2 / leaf-K2 / spanning-K2）· 核对层

module Sovereign.Topology.Graphs.Trees where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)

open import Sovereign.Topology.Graphs.GraphBasic using (Graph; V; adj; adj-sym; adj-irrefl)
open import Sovereign.Topology.Graphs.Connectivity using (Reachable; reflR; stepR; Connected)

------------------------------------------------------------------------
-- 基础件层：∈ᵥ / NoDup（自含——关系入定义）
------------------------------------------------------------------------

data _∈ᵥ_ {A : Set} : A → List A → Set where
  ev-here  : ∀ {x} {xs} → x ∈ᵥ (x ∷ xs)
  ev-there : ∀ {x y} {xs} → x ∈ᵥ xs → x ∈ᵥ (y ∷ xs)

data NoDup {A : Set} : List A → Set where
  nd-[] : NoDup []
  nd-∷  : ∀ {x} {xs} → (x ∈ᵥ xs → ⊥) → NoDup xs → NoDup (x ∷ xs)

------------------------------------------------------------------------
-- 主引理层：Chain / Cycle / Acyclic / Tree
------------------------------------------------------------------------

-- 顶点列路径：Chain G x z vs = x 经内部顶点表 vs 到 z 的途径（逐边生成）
data Chain (G : Graph) : V G → V G → List (V G) → Set where
  chn : ∀ (x : V G) → Chain G x x []
  chs : ∀ {x y z : V G} {vs} → adj G x y → Chain G y z vs → Chain G x z (y ∷ vs)

-- 简单圈：开口途径 + 收口边 + 顶点无重复 + 长度下界
--   （Chain 的终点 = 末内部顶点，故闭圈 = Chain x z vs ⊗ 收口边 adj z x；
--     2 ≤ |vs| 保证 ≥3 顶点——二步假圈 a→b→a（|vs|=1）排除）
Cycle : (G : Graph) (x : V G) (vs : List (V G)) → Set
Cycle G x vs =
  Σ (V G) λ z → Chain G x z vs × adj G z x × NoDup (x ∷ vs) × (2 ≤ length vs)

Acyclic : (G : Graph) → Set
Acyclic G = ∀ (x : V G) (vs : List (V G)) → Cycle G x vs → ⊥

Tree : (G : Graph) → Set
Tree G = Connected G × Acyclic G

-- 生成树：顶点满射 + 边保持的树子图（toV 承载同载体/覆盖口径）
record SpanningTree (G : Graph) : Set₁ where
  field
    T        : Graph
    st-tree  : Tree T
    toV      : V T → V G
    st-sub   : ∀ {x y : V T} → adj T x y → adj G (toV x) (toV y)
    toV-surj : ∀ (z : V G) → Σ (V T) λ x → toV x ≡ z

-- 邻接计数 / 叶（枚举参数形——与 GraphBasic.count-adj 同口径，自含免签名耦合）
nadj : (G : Graph) (x : V G) (enum : List (V G))
     → (dec : (a b : V G) → Dec (adj G a b)) → ℕ
nadj G x [] dec = zero
nadj G x (y ∷ ys) dec with dec y x
... | yes _ = suc (nadj G x ys dec)
... | no  _ = nadj G x ys dec

IsLeaf : (G : Graph) (x : V G) (enum : List (V G))
       → (dec : (a b : V G) → Dec (adj G a b)) → Set
IsLeaf G x enum dec = nadj G x enum dec ≡ 1

------------------------------------------------------------------------
-- 实例层：Bit / K2（K2 是树、无圈、双叶、自身生成树——全证）
------------------------------------------------------------------------

data Bit : Set where
  b0 b1 : Bit

flip : Bit → Bit
flip b0 = b1
flip b1 = b0

flip-invol : ∀ b → flip (flip b) ≡ b
flip-invol b0 = refl
flip-invol b1 = refl

neq01 : b0 ≡ b1 → ⊥
neq01 ()

neq10 : b1 ≡ b0 → ⊥
neq10 ()

adj2 : Bit → Bit → Set
adj2 x y = x ≡ y → ⊥

adj2-sym : ∀ {x y} → adj2 x y → adj2 y x
adj2-sym f e = f (sym e)

adj2-irrefl : ∀ {x} → adj2 x x → ⊥
adj2-irrefl f = f refl

-- 邻接 ⟹ 第二顶点 = flip 第一顶点（K2 结构刻画）
y-flip : ∀ x y → adj2 x y → y ≡ flip x
y-flip b0 b0 h = ⊥-elim (h refl)
y-flip b0 b1 h = refl
y-flip b1 b0 h = refl
y-flip b1 b1 h = ⊥-elim (h refl)

K2 : Graph
K2 = record
  { V          = Bit
  ; adj        = adj2
  ; adj-sym    = adj2-sym
  ; adj-irrefl = adj2-irrefl
  }

dec-adj2 : (a b : Bit) → Dec (adj2 a b)
dec-adj2 b0 b0 = no (λ f → f refl)
dec-adj2 b0 b1 = yes neq01
dec-adj2 b1 b0 = yes neq10
dec-adj2 b1 b1 = no (λ f → f refl)

-- 辅助：≤ 形消解件（长度下界收口）
sn≰0 : ∀ {n} → suc n ≤ 0 → ⊥
sn≰0 ()

len≤1-vs-2≤ : ∀ {n} → 2 ≤ n → n ≤ 1 → ⊥
len≤1-vs-2≤ (s≤s (s≤s h)) (s≤s g) = sn≰0 g

-- (a) 途径顶点取值 ∈ {x, flip x}
chain-K2-vals : ∀ {x y} (vs : List Bit) → Chain K2 x y vs
              → ∀ v → v ∈ᵥ vs → (v ≡ x ⊎ v ≡ flip x)
chain-K2-vals [] (chn x) v ()
chain-K2-vals (y ∷ vs) (chs {x = x} {y = y'} {z = z} h c) v m with m
... | ev-here = inj₂ (y-flip x y' h)
... | ev-there m' with chain-K2-vals vs c v m'
... | inj₁ q = inj₂ (trans q (y-flip x y' h))
... | inj₂ q = inj₁ (trans q (trans (cong flip (y-flip x y' h)) (flip-invol x)))

-- (b) NoDup (x ∷ vs) ⟹ vs 元素 ≠ x
nodup-head-ne : ∀ {x} {vs : List Bit} → NoDup (x ∷ vs)
              → ∀ v → v ∈ᵥ vs → v ≡ x → ⊥
nodup-head-ne (nd-∷ fx _) v m e = fx (subst (λ q → q ∈ᵥ _) e m)

-- (c) 两点值 + 无重复 ⟹ 长度 ≤ 1
nodup-2vals-len : ∀ {x} (vs : List Bit) → NoDup (x ∷ vs)
                → (∀ v → v ∈ᵥ vs → (v ≡ x ⊎ v ≡ flip x))
                → length vs ≤ 1
nodup-2vals-len [] _ _ = z≤n
nodup-2vals-len (v ∷ []) _ _ = s≤s z≤n
nodup-2vals-len (v ∷ w ∷ ws) (nd-∷ fx (nd-∷ fv ndw)) ih
  with ih v ev-here | ih w (ev-there ev-here)
... | inj₁ ev | _ = ⊥-elim (fx (subst (λ t → t ∈ᵥ (v ∷ w ∷ ws)) ev ev-here))
... | inj₂ _ | inj₁ ew = ⊥-elim (fx (subst (λ t → t ∈ᵥ (v ∷ w ∷ ws)) ew (ev-there ev-here)))
... | inj₂ ep | inj₂ eq =
      ⊥-elim (fv (subst (λ t → t ∈ᵥ (w ∷ ws)) (sym (trans ep (sym eq))) ev-here))

-- K2 无圈（全证）
acyclic-K2 : Acyclic K2
acyclic-K2 x vs (_ , c , _ , nd , le) = len≤1-vs-2≤ le (nodup-2vals-len vs nd sub)
  where
    sub : ∀ v → v ∈ᵥ vs → (v ≡ x ⊎ v ≡ flip x)
    sub v m = chain-K2-vals vs c v m

-- K2 连通（全证）
connected-K2 : Connected K2
connected-K2 b0 b0 = reflR b0
connected-K2 b0 b1 = stepR neq01 (reflR b1)
connected-K2 b1 b0 = stepR neq10 (reflR b0)
connected-K2 b1 b1 = reflR b1

tree-K2 : Tree K2
tree-K2 = connected-K2 , acyclic-K2

-- K2 双叶（全证）
leaf-K2-b0 : IsLeaf K2 b0 (b0 ∷ b1 ∷ []) dec-adj2
leaf-K2-b0 = refl

leaf-K2-b1 : IsLeaf K2 b1 (b0 ∷ b1 ∷ []) dec-adj2
leaf-K2-b1 = refl

-- K2 的自身生成树（全证）
spanning-K2 : SpanningTree K2
spanning-K2 = record
  { T        = K2
  ; st-tree  = tree-K2
  ; toV      = λ x → x
  ; st-sub   = λ h → h
  ; toV-surj = λ z → z , refl
  }

------------------------------------------------------------------------
-- 核对层
------------------------------------------------------------------------

-- 三重复顶点列必非 NoDup（无圈判据的反面核对）
check-nodup-ab-a : NoDup (b0 ∷ b1 ∷ b0 ∷ []) → ⊥
check-nodup-ab-a (nd-∷ f _) = f (ev-there ev-here)

check-tree-K2 : Tree K2
check-tree-K2 = tree-K2

check-leaf-K2 : nadj K2 b0 (b0 ∷ b1 ∷ []) dec-adj2 ≡ 1
check-leaf-K2 = leaf-K2-b0

-- 立界注记（诚实边界）：
--   (i) 一般树的叶存在性（有限树 ≥2 顶点 ⟹ ∃ 度 1 顶点——需有限性+删叶归纳，~80-120 行）
--   (ii) 唯一路径刻画（Tree ⟺ 任意两点间途径唯一——~100-150 行）
--   (iii) |E| = |V|-1 等价刻画（需边/顶点计数框架）
--   (iv) 生成树计数 = Kirchhoff 矩阵-树定理衔接（Problem/Hodge/KirchhoffZ 既有件——
--        本模块 Tree 口径与其计数面的桥接注记：Kirchhoff 计数的是生成树个数，
--        本模块 SpanningTree record 为其载体形；两面对接留桥批次）
